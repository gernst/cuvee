package cuvee.lemmas.recognize

import cuvee.lemmas.Def
import cuvee.lemmas.C
import cuvee.pure._
import cuvee.imp.WP

object Compare {
  def main(args: Array[String]) {
    val (cmds, st) = cuvee.boogie.parse("examples/boogie/debug.bpl")
    val (decls, eqs, defs) = cuvee.lemmas.prepare(cmds, st)

    val rules = eqs.groupBy(_.fun)
    val constrs = st.constrs

    for (
      df <- defs; dg <- defs if df.fun != dg.fun;
      (dpre, xs, pre, lhs, rhs) <- compare(df, dg, rules, constrs)
    ) try {
      val eq = Forall(xs, pre ==> Eq(lhs, rhs))
      println(eq)
      println(dpre)
      println()
    } catch {
      case _: Exception =>
        println("failed: " + df.fun + " ?= " + dg.fun)
    }
  }

  object CanIgnore extends Exception
  // object CannotCompare extends Exception

  def splitArgs[A](fargs: List[A], i: Int, gargs: List[A], j: Int) = {
    import cuvee.ListOps
    (fargs(i), gargs(j), (fargs removed i), (gargs removed j))
  }

  def compare(
      df: Def,
      dg: Def,
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun]
  ): List[(Def, List[Var], Expr, Expr, Expr)] = {
    for (
      (t, i) <- df.args.zipWithIndex if df.isMatchingPosition(i);
      (t_, j) <- dg.args.zipWithIndex if dg.isMatchingPosition(j)
      if t == t_;
      res <- compare(df, i, dg, j, rules, constrs)
    )
      yield res
  }

  def compare(
      df: Def,
      i: Int,
      dg: Def,
      j: Int,
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun]
  ): Option[(Def, List[Var], Expr, Expr, Expr)] = {
    val Def(f, fcases) = df
    val Def(g, gcases) = dg
    require(f.params.isEmpty)
    require(g.params.isEmpty)

    try {
      val (t, t_, fts, gts) = splitArgs(f.args, i, g.args, j)
      require(t == t_, "type mismatch: " + t + " and " + t_)

      val pre =
        Fun("pre_" + f.name + ":" + i + "_" + g.name + ":" + j, Nil, t :: fts ::: gts, Sort.bool)

      val precases =
        for (
          cf <- fcases;
          cg <- gcases;
          cpre <- compare(pre, f, cf, i, g, cg, j, rules, constrs)
        )
          yield cpre

      val x = Var("x", t)
      val ys = Expr.vars("y", fts)
      val zs = Expr.vars("z", gts)
      val xs = x :: ys ::: zs

      val lhs = App(f, ys patch (i, List(x), 0))
      val rhs = App(g, zs patch (j, List(x), 0))

      val isNontrivial =
        (precases exists { c => !c.isRecursive(pre) && c.body != False }) &&
          (precases exists { c => c.isRecursive(pre) })

      if (isNontrivial) {
        // val eq = Forall(xs, App(pre, xs) ==> Eq(lhs, rhs))
        val dpre = Def(pre, precases)
        Some((dpre, xs, App(pre, xs), lhs, rhs))
      } else {
        None
      }
    } catch {
      // case CannotCompare =>
      //   None
      case _: Type.CannotUnify =>
        None
    }
  }

  def compare(
      pre: Fun,
      f: Fun,
      cf: C,
      i: Int,
      g: Fun,
      cg: C,
      j: Int,
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun]
  ): List[C] = {
    val re = Expr.fresh(cf.bound)
    val C(fpats, fguard, fbody) = cf
    val C(gpats, gguard, gbody) = cg replace re
    // println("==================")
    // println(fpats)
    // println(gpats)
    // println("==================")
    require(
      fpats.free disjoint gpats.free,
      "patterns are not disjount (internal error): " + fpats + " and " + gpats + " of " + f + " and " + g
    )

    try {
      val (pat, pat_, fpats_, gpats_) = splitArgs(fpats, i, gpats, j)
      val (ty, su) = Expr.unify(pat, pat_)
      require(ty.isEmpty)
      require((pat subst su) == (pat_ subst su))
      // if(su.nonEmpty)
      // println("unify " + pat + " and " + pat_ + " = " + su)

      var guard = (fguard ++ gguard) subst su

      guard = Simplify.simplify(guard, rules, constrs)
      guard = guard.distinct filterNot (_ == True)

      if (guard contains False) {
        Nil
      } else if (guard exists { phi => guard exists { psi => Simplify.not(phi) == psi } }) {
        Nil
      } else {
        val pats = fpats_ ++ gpats_
        // maybe we can simplify something wrt. su
        val fbody_ = Simplify.simplify(fbody subst su, rules, constrs)
        val gbody_ = Simplify.simplify(gbody subst su, rules, constrs)
        val body = meet(pre, f, fbody_, i, g, gbody_, j, constrs)

        // simplify again
        val body_ = Simplify.simplify(And(body), rules, constrs)
        List(C((pat subst su) :: pats, guard, body_))
      }
    } catch {
      case CanIgnore =>
        Nil
      case _: Expr.CannotUnify =>
        Nil
    }
  }

  def meet(
      pre: Fun,
      f: Fun,
      fexpr: Expr,
      i: Int,
      g: Fun,
      gexpr: Expr,
      j: Int,
      constrs: Set[Fun]
  ): List[Expr] = {
    (fexpr, gexpr) match {
      case (App(Inst(`f`, _), fargs), App(Inst(`g`, _), gargs)) =>
        val (fa, ga, fexprs, gexprs) = splitArgs(fargs, i, gargs, j)
        val rest = App(pre, fa :: fexprs ::: gexprs) :: meet(pre, f, fa, i, g, ga, j, constrs)
        if (fa == ga) rest
        else Eq(fa, ga) :: rest

      case (App(Inst(h, _), fargs), App(Inst(h_, _), gargs)) if h == h_ =>
        meets(pre, f, fargs, i, g, gargs, j, constrs)

      // NO: this should result in False as result
      // case (App(Inst(h, _), fargs), App(Inst(h_, _), gargs))
      //     if h != h_ && (constrs contains h) && (constrs contains h_) =>
      //   throw CanIgnore

      case _ if fexpr == gexpr =>
        Nil

      // non-recursive cases, resp. non-recursive part of the body
      case _ if !(f in fexpr) && !(g in gexpr) =>
        List(Eq(fexpr, gexpr))

      case _ =>
        List(False)
    }
  }

  def meets(
      pre: Fun,
      f: Fun,
      fexprs: List[Expr],
      i: Int,
      g: Fun,
      gexprs: List[Expr],
      j: Int,
      constrs: Set[Fun]
  ): List[Expr] = {
    require(fexprs.length == gexprs.length)
    for (
      (fexpr, gexpr) <- (fexprs zip gexprs);
      phi <- meet(pre, f, fexpr, i, g, gexpr, j, constrs)
    ) yield phi
  }
}

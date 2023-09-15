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
      (pre, eq) <- compare(df, dg, rules, constrs)
    ) try {
      println(eq)
      println(pre)
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
  ): List[(Def, Expr)] = {
    for (
      (t, i) <- df.args.zipWithIndex if df.isMatchingPosition(i);
      (t_, j) <- dg.args.zipWithIndex if dg.isMatchingPosition(j)
      if t == t_;
      (dpre, eq) <- compare(df, i, dg, j, rules, constrs)
    )
      yield (dpre, eq)
  }

  // TODO: make sure cases are using disjoint type parameters and variables
  def compare(
      df: Def,
      i: Int,
      dg: Def,
      j: Int,
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun]
  ): Option[(Def, Expr)] = {
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
      val ys = Expr.vars("ys", fts)
      val zs = Expr.vars("zs", gts)
      val xs = x :: ys ::: zs

      val lhs = App(f, ys patch (i, List(x), 0))
      val rhs = App(g, zs patch (j, List(x), 0))

      val eq = Forall(xs, App(pre, xs) ==> Eq(lhs, rhs))
      val dpre = Def(pre, precases)
      Some((dpre, eq))
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
    val C(fpats, fguard, fbody) = cf
    val C(gpats, gguard, gbody) = cg refresh cf.bound

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
        val fbody_ = fbody subst su // we assume the functions are already normalized!
        val gbody_ = gbody subst su
        val body = meet(pre, f, fbody_, i, g, gbody_, j, constrs)
        val body_ = Simplify.simplify(body, rules, constrs)

        // possibly simplify guard here
        List(C((pat subst su) :: pats, guard, And(body_)))
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

      case (App(Inst(h, _), fargs), App(Inst(h_, _), gargs))
          if h != h_ && (constrs contains h) && (constrs contains h_) =>
        throw CanIgnore

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

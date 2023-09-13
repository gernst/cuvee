package cuvee.lemmas

import easyparse.Control
import cuvee.pure._
import cuvee.util.Matching

object Known {
  var debug = true

  def main(args: Array[String]) {}

  def key(f: Fun)(c: C) = c match {
    case C(_, _, App(inst, args)) if inst.fun == f =>
      None // tail-recursive calls: delay matching

    case C(_, _, x: Var)          => None
    case C(_, _, App(inst, args)) => Some(inst.fun)
  }

  def prio(a: Option[Fun], b: Option[Fun]) = (a, b) match {
    case (None, None)       => true // stable
    case (None, Some(_))    => false
    case (Some(_), None)    => true
    case (Some(a), Some(b)) => a.name.toLabel < b.name.toLabel
  }

  def bind(
      cf: List[
        (C, Int)
      ], // the numbers are the ordering of cases in the definition
      cg: List[(C, Int)],
      p: List[Int],
      ty: Map[Param, Type],
      su: Map[Var, Expr] = Map()
  ) = {}

  def check(
      cases: List[(List[(C, Int)], List[(C, Int)])],
      p: List[Int] = Nil, // permutation that reorders function arguments
      ty: Map[Param, Type] = Map() // typing applies to the entire function
  ): List[(List[Int], Map[Param, Type])] =
    cases match {
      case Nil =>
        List((p, ty))

      case (fs, gs) :: rest if fs.length != gs.length =>
        Nil

      case (fs, gs) :: rest =>
        check(rest)
    }

  def invert(a: List[Int]) = {
    val b = a.zipWithIndex
    val c = b.sortBy(_._1)
    val (_, d) = c.unzip
    d
  }

  def foo(f: Fun, i: Int, cs: List[C]): Int = {
    val ks = cs.zipWithIndex collect {
      case (C(args, guard, x: Var), k) if (args indexOf x) == i =>
        k
    }

    ks match {
      case Nil => 0
      case List(k) =>
        k
      case _ =>
        // println("  multiple occurrences of argument at " + i)
        // println("  " + f)
        // println("  " + ks.mkString(" "))
        ks.sum
    }
  }

  def known(df: Def, defs: List[Def]): List[(Def, Map[Param, Type], List[Int])] = {
    for (
      dg <- defs;
      (ty, perm) <- known(df, dg)
    )
      yield (dg, ty, perm)
  }

  // dg is known already and we want to check whether df matches
  def known(df: Def, dg: Def): Option[(Map[Param, Type], List[Int])] = {
    // Merge.merge(df, dg)
    if (
      df.fun != dg.fun &&
      df.fun.args.length == dg.fun.args.length &&
      // df.fun.args == dg.fun.args &&
      // df.fun.args == dg.fun.args &&
      // df.fun.res == dg.fun.res &&
      df.cases.length == dg.cases.length
    ) {
      val Def(f, fcases) =
        df // Check: can we guarantee order via fuse/factoring maintained?
      val Def(g, gcases) = dg

      // println(df.fun.name + "#" + Def.hash(df) + " ?= " + dg.fun.name + "#" + Def.hash(dg))
      // val x = cuvee.keyedPairings(fcases, gcases, key(f), key(g), prio)
      // val y = check(x)
      val fg = Set(f, g)

      val fcases_ = fcases.sortBy(Def.hash(fg, _))
      val gcases_ = gcases.sortBy(Def.hash(fg, _))

      ??? // this idea of sorting by has code is fundamentally broken!!
      
      // use this code to debug hash code problems
      if (debug) {
        println("======================")
        println("comparing: " + f.name + "  and  " + g.name)
        println(fcases_ map (Def.hash(fg, _)))
        println(gcases_ map (Def.hash(fg, _)))
        println("======================")
      }

      val F = f.args.zipWithIndex.sortBy { case (t, i) =>
        Def.hash(t) -> foo(f, i, fcases_)
      }
      val G = g.args.zipWithIndex.sortBy { case (t, i) =>
        Def.hash(t) -> foo(g, i, gcases_)
      }
      val (ftypes, fp) = F.unzip
      val (gtypes, gp) = G.unzip

      val ok_ =
        try {
          val su = Type.binds(gtypes, g.res, ftypes, f.res, Map())

          val ok_ = (fcases_ zip gcases_) forall {
            case (cf, cg) => {
              if (debug) {
                println("matching pair of case: ")
                println("  " + cf)
                println("  " + cg)
              }
              val C(fargs, fguard, fbody) = cf
              val C(gargs, gguard, gbody) = cg inst su

              ok(
                f,
                fp,
                fargs,
                fguard,
                fbody,
                g,
                gp,
                gargs,
                gguard,
                gbody,
                su
              )
            }
          }

          if (ok_) {
            Some(su)
          } else {
            None
          }
        } catch {
          case _: Type.CannotBind =>
            if (debug)
              println("failed to match types: " + f.name + " and " + g.name)
            None
        }

      ok_ match {
        case Some(su) =>
          // val xs = Expr.vars("x", ftypes)
          // val fm = invert(fp)
          val perm = invert(gp) map fp

          // val lhs = App(f, fm map xs)
          // val rhs = App(g, gm map (fp map xs))
          // val eq = Rule(lhs, rhs, True)

          // println("representation: " + eq)
          Some(su -> perm)

        case None =>
          if (Def.hash(df) == Def.hash(dg)) {
            // println(
            //   "  potentially missed equivalence " + f.name + " == " + g.name
            // )
            // println("  definitions are structurally similar when ignoring variable names")
            // println(df)
            // println(dg)
          }

          if (df.fun.name == dg.fun.name) {
            println("failed to recognize function with same name")
            println(df)
            println(dg)
            ???
          }

          None
      }
    } else {
      if (debug) {
        println("  not possible: " + df.fun.name + " ?= " + dg.fun.name)
        println("funs  length diff? " + (df.fun != dg.fun))
        println("args  length same? " + (df.fun.args.length == dg.fun.args.length))
        println("cases length same? " + (df.cases.length == dg.cases.length))
      }

      None
    }
  }

  def ok(
      f: Fun,
      fp: List[Int],
      fargs: List[Expr],
      fguard: List[Expr],
      fbody: Expr,
      g: Fun,
      gp: List[Int],
      gargs: List[Expr],
      gguard: List[Expr],
      gbody: Expr,
      su: Map[Param, Type]
  ): Boolean = {
    if (debug) {
      println("checking ")
      println(fargs.mkString(" ") + ". " + fbody)
      println(gargs.mkString(" ") + ". " + gbody)
    }

    var ok = true
    var re: Map[Var, Var] = Map()

    def rename(a: Expr, b: Expr): Unit = (a, b) match {
      case (x: Var, y: Var) =>
        re += (x -> y)
      case (App(Inst(f, fs), as), App(Inst(g, gs), bs)) if f == g =>
        renames(as, bs)
      case _ =>
        if (debug)
          println("no match: " + a + " != " + b)
        ok = false
    }

    def renames(as: List[Expr], bs: List[Expr]): Unit = (as, bs) match {
      case (Nil, Nil) =>
      case (a :: as, b :: bs) =>
        rename(a, b)
        renames(as, bs)
    }

    renames(fp map fargs, gp map gargs)

    def equal(a: Expr, b: Expr): Boolean = (a, b) match {
      case (x: Var, y: Var) if x == y =>
        true

      case (x: Lit, y: Lit) if x == y =>
        true

      case (Eq(l1, r1), Eq(l2, r2)) =>
        val ok1 = equal(l1, l2) && equal(r1, r2)
        val ok2 = equal(l1, r2) && equal(r1, l2)
        ok1 || ok2

      case (Plus(fa), Plus(ga)) =>
        // XXX: this is a bit of a hack for: size:0:mirror on trees :/
        val results = Matching.relate(
          fa,
          ga,
          false,
          { (a: Expr, b: Expr, ok: Boolean) =>
            if (ok) List(() -> true)
            else if (equal(a, b)) List(() -> true)
            else Nil
          }
        )

        results.exists(_._4)

      case (App(Inst(`f`, _), fargs), App(Inst(`g`, _), gargs)) =>
        equals(fp map fargs, gp map gargs)

      case (App(Inst(f, fs), as), App(Inst(g, gs), bs)) if f == g =>
        equals(as, bs)

      case _ =>
        if (debug)
          println("not equal: " + a + " != " + b)
        false
    }

    def equals(as: List[Expr], bs: List[Expr]): Boolean = (as, bs) match {
      case (Nil, Nil) =>
        true
      case (a :: as, b :: bs) =>
        equal(a, b) && equals(as, bs)
      case _ =>
        if (debug)
          println("no match: " + as + " != " + bs)
        false
    }

    if (ok) {
      ok = equals(fguard rename re, gguard) && equal(fbody rename re, gbody)
      if (!ok && debug)
        println("not equals: ", (fguard rename re, gguard), (fbody rename re, gbody))
      // println(" = " + ok)
      // val _fguard = fguard rename re
      // val _gguard = gguard rename re

      // val _fbody = fbody rename re bottomup {
      //   case App(Inst(`f`, _), args) => App(Inst(g, su), fp map args)
      //   case e                       => e
      // }

      // val _gbody = gbody rename re bottomup {
      //   case App(Inst(`g`, _), args) => App(Inst(g, su), gp map args)
      //   case e                       => e
      // }

      // ok = _fguard == _gguard && _fbody == _gbody

      // if (!ok && _fguard != _gguard)
      //   println("; guards different: " + _fguard + " and " + _gguard)
      // if (!ok && _fbody != _gbody)
      //   println("; bodies different: " + _fbody + " and " + _gbody)
    }

    ok
  }
}

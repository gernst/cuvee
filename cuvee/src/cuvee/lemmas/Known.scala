package cuvee.lemmas

import cuvee.pure._

class Known(lemma: Lemma) {
  // Note: do not try to specialize known definitions,
  //       this is done via factoring
  def known(df: Def[Norm], all: Iterable[Def[Norm]]): Iterable[Rule] = {
    all flatMap { known(df, _) }
  }

  def known(df: Def[Norm], dg: Def[Norm]): Option[Rule] = {
    if (
      df.fun != dg.fun &&
      df.fun.params == dg.fun.params &&
      df.fun.args == dg.fun.args &&
      df.fun.res == dg.fun.res &&
      df.cases.length == dg.cases.length
    ) {
      val Def(f, fcases) =
        df // Check: can we guarantee order via fuse/factoring maintained?
      val Def(g, gcases) = dg

      val ok_ =
        (fcases zip gcases) forall { case (cf, cg) =>
          ok(f, cf, g, cg)
        }

      if (ok_) {
        val xs = Util.vars("x", f.args)
        val lhs = App(f, xs)
        val rhs = App(g, xs)
        val eq = Rule(lhs, rhs, True)
        // println("can represent " + f + " as " + g)
        Some(eq)
      } else {
        None
      }
    } else {
      None
    }
  }

  def ok(f: Fun, cf: Norm, g: Fun, cg: Norm): Boolean = {
    ok(f, cf flat g, g, cg flat g) // Note: put in the *same* function name!
  }

  def ok(f: Fun, cf: Flat, g: Fun, cg: Flat): Boolean = {
    val Flat(fargs, fguard, fbody) = cf
    val Flat(gargs, gguard, gbody) = cg

    var ok = true
    var re: Map[Var, Var] = Map()

    def rename(a: Expr, b: Expr): Unit = (a, b) match {
      case (x: Var, y: Var) =>
        re += (x -> y)
      case (App(f, as), App(g, bs)) if f == g =>
        renames(as, bs)
      case _ =>
        ok = false
    }

    def renames(as: List[Expr], bs: List[Expr]): Unit = (as, bs) match {
      case (Nil, Nil) =>
      case (a :: as, b :: bs) =>
        rename(a, b)
        renames(as, bs)
    }

    renames(fargs, gargs)

    if (ok) {
      val _fguard = fguard rename re
      val _gguard = gguard rename re

      val _fbody = fbody rename re
      val _gbody = gbody rename re
      ok = _fguard == _gguard && _fbody == _gbody

      // if(!ok && _fguard != _gguard)
      //   println("; guards different: " + _fguard + " and " + _gguard)
      // if(!ok && _fbody != _gbody)
      //   println("; bodies different: " + _fbody + " and " + _gbody)
    }

    ok
  }
}

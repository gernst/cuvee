package cuvee.lemmas

import cuvee.pure._

object Fuse {
  def fuse(df: Def, dg: Def, pos: Int): Def = {
    // merge cases of df with those of dg, such that

    // f(x, g(y))
    // fg(x, y) has
    // - cases for y as g
    // - cases for x as f, however, we pair them according to the respective result
    // *if* it is possible to match it statically

    for (
      Case(fargs, fguard, fas, fbs, fcs, fd) <- df.cases;
      Case(gargs, gguard, gas, gbs, gcs, gd) <- dg.cases
    ) {
      ???
    }

    ???
  }

  // collect cases of a definition that match a particular pattern
  // possibly unfolding other function definitions, too (not implemented yet);
  // make sure the variables in pat do not clash with those in the arguments of the cases!
  // this function probably works less well with normalized definitions (Split.scala)
  def expose(
      pat: Expr,
      body: Expr,
      cases: List[(List[Expr], Expr)]
  ): List[(List[Expr], Expr)] = {
    // require(
    //   pat.typ == f.fun.res,
    //   "cannot expose " + pat.toStringTyped + " over " + f.fun
    // )

    for (
      (args, d) <- cases;
      (args_, su) <- expose(pat, args, d)
    )
      yield {
        (args_, body subst su)
      }
  }

  def expose(
      pat: Expr,
      args: List[Expr],
      d: Expr,
      su: Map[Var, Expr] = Map()
  ): Option[(List[Expr], Map[Var, Expr])] =
    (pat, d) match {
      case (x: Var, _) if su contains x =>
        if (su(x) == d) {
          Some((args, su))
        } else {
          println("refute exposing " + x + " over " + d)
          println("already bound to " + su(x))
          None
        }

      case (x: Var, _) =>
        Some((args, su + (x -> d)))

      // constructor match: we can recurse into the arguments
      // Note: pat should only have constructors in function position
      case (App(fun1, _, pats), App(fun2, _, ds)) if fun1 == fun2 =>
        expose(pats, args, ds, su)

      // unconstrained argument: we can chain the pattern to the top-level
      // TODO: later possibly remove x from the vars of the case
      case (_, x: Var) if args contains x =>
        val pos = args indexOf x
        val args_ = args updated (pos, pat)
        Some((args_, su))

      case _ =>
        println("refute exposing " + pat + " over " + d)
        None
    }

  def expose(
      pats: List[Expr],
      args: List[Expr],
      ds: List[Expr],
      su: Map[Var, Expr]
  ): Option[(List[Expr], Map[Var, Expr])] =
    (pats, ds) match {
      case (Nil, Nil) =>
        Some((args, su))

      case (pat :: pats, d :: ds) =>
        expose(pat, args, d, su) match {
          case None =>
            None
          case Some((args_, su_)) =>
            expose(pats, args_, ds, su_)
        }
    }
}

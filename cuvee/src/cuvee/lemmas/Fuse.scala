package cuvee.lemmas

import cuvee.pure._
import cuvee.StringOps

object Fuse {
  def fuse(df: Def[Flat], dg: Def[Flat]): List[(Def[Flat], Rule)] = {
    val typ = dg.fun.res
    for (
      (`typ`, pos) <- df.fun.args.zipWithIndex;
      dfg <- fuse(df, dg, pos) if isRecursivePosition(df, pos)
    )
      yield dfg
  }

  def isRecursivePosition(df: Def[Flat], pos: Int): Boolean = {
    df.cases exists { case Flat(args, guard, body) =>
      args(pos).isInstanceOf[App]
    }
  }

  def fuse(
      df: Def[Flat],
      dg: Def[Flat],
      pos: Int
  ): Option[(Def[Flat], Rule)] = {
    val Def(f, fcases) = df
    val Def(g, gcases) = dg

    require(
      f.args(pos) == g.res,
      "cannot fuse " + f + " with " + g + " at pos " + pos
    )

    val name = f.name + "_" + g.name + "_" + pos
    val params = f.params ++ g.params
    val args = f.args patch (pos, g.args, 1)
    val res = f.res
    val fg = Fun(name, params.distinct, args, res)

    try {
      val cases =
        for (
          gcase <- gcases;
          flat <- fuse(f, g, fg, fcases, gcase, pos)
        )
          yield flat

      val dfg = Def(fg, cases)

      val xs =
        for ((t, i) <- f.args.zipWithIndex)
          yield Var("x", t, Some(i))
      val ys =
        for ((t, i) <- g.args.zipWithIndex)
          yield Var("y", t, Some(i))

      val lhs = App(f, xs updated (pos, App(g, ys)))
      val rhs = App(fg, xs patch (pos, ys, 1))
      val rule = Rule(lhs, rhs, True)

      Some((dfg, rule))
    } catch {
      case _: NotImplementedError =>
        None
    }
  }

  def fuse(
      f: Fun,
      g: Fun,
      fg: Fun,
      fcases: List[Flat],
      gcase: Flat,
      pos: Int
  ): List[Flat] =
    gcase match {
      case Flat(gargs, gguard, x: Var) =>
        val fargs =
          for ((t, i) <- f.args.zipWithIndex)
            yield Var("x", t, Some(i))
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs updated (pos, x)
        val guard = gguard
        val body = App(f, recs)
        List(Flat(args, guard, body))

      case Flat(gargs, gguard, App(`g`, _, grecs)) =>
        val fargs =
          for ((t, i) <- f.args.zipWithIndex)
            yield Var("x", t, Some(i))
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs patch (pos, grecs, 1)
        val guard = gguard
        val body = App(fg, recs)
        List(Flat(args, guard, body))

      case Flat(gargs, gguard, gbody) =>
        val fpats = fcases flatMap (_.args)
        val critical = gcase.args.free & fpats.free
        val re = Expr.fresh(critical)
        val fcases_ = fcases map (_ rename re)

        for (
          Flat(fargs, fguard, fbody) <- fcases_;
          (gargs_, su) <- expose(f, g, fg, fargs(pos), gargs, gbody)
        ) yield {
          val args = fargs patch (pos, gargs_, 1)
          val guard = fguard ++ gguard
          val body = recurse(f, g, fg, pos, fbody, su) // fbody subst su
          Flat(args, guard, body)
        }
    }

  def recurse(
      f: Fun,
      g: Fun,
      fg: Fun,
      pos: Int,
      body: Expr,
      su: Map[Var, Expr]
  ): Expr =
    body match {
      case x: Var if su contains x =>
        su(x) // non-recursive matched case
      case x: Var =>
        x
      case l: Lit =>
        l
      case App(
            `f`,
            inst,
            args
          ) => // keep inst to prevent making it more generic
        val args_ = args map (recurse(f, g, fg, pos, _, su))
        args_(pos) match {
          case App(`g`, _, args) =>
            val res = App(fg, args_ patch (pos, args, 1))
            res
          case _ =>
            App(f, inst, args_)
        }
      case App(h, inst, args) =>
        val args_ = args map (recurse(f, g, fg, pos, _, su))
        App(h, inst, args_)
    }

  // HACK: don't refute when the body is some function
  val constructors = Set("nil", "cons")

  // collect cases of a definition that match a particular pattern
  // possibly unfolding other function definitions, too (not implemented yet);
  // make sure the variables in pat do not clash with those in the arguments of the cases!
  // this function probably works less well with normalized definitions (Split.scala)
  def expose(
      f: Fun,
      g: Fun,
      fg: Fun,
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
          println("; cannot expose " + x + " over " + d)
          println("; already bound to " + su(x))
          println(fg)
          println()
          ???
        }

      case (x: Var, _) =>
        Some((args, su + (x -> d)))

      // constructor match: we can recurse into the arguments
      // Note: pat should only have constructors in function position
      case (App(fun1, _, pats), App(fun2, _, ds))
          if constructors contains fun2.name =>
        if (fun1 == fun2) {
          expose(f, g, fg, pats, args, ds, su)
        } else {
          // println("refute exposing " + pat + " over " + d)
          None
        }

      // unconstrained argument: we can chain the pattern to the top-level
      // TODO: later possibly remove x from the vars of the case
      case (_, x: Var) if args contains x =>
        val pos = args indexOf x
        val args_ = args updated (pos, pat)
        Some((args_, su))

      case _ =>
        println("; cannot expose " + pat + " over " + d)
        println("; " + fg)
        println()
        ???
    }

  def expose(
      f: Fun,
      g: Fun,
      fg: Fun,
      pats: List[Expr],
      args: List[Expr],
      ds: List[Expr],
      su: Map[Var, Expr]
  ): Option[(List[Expr], Map[Var, Expr])] =
    (pats, ds) match {
      case (Nil, Nil) =>
        Some((args, su))

      case (pat :: pats, d :: ds) =>
        expose(f, g, fg, pat, args, d, su) match {
          case None =>
            None
          case Some((args_, su_)) =>
            expose(f, g, fg, pats, args_, ds, su_)
        }
    }
}

package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.StringOps

class Fuse(st: State) {
  object CannotFuse extends Exception

  def fuse(df: Def[Flat], dg: Def[Flat]): List[(Def[Flat], Rule)] = {
    for (
      (typ, pos) <- df.fun.args.zipWithIndex
      if typ == dg.fun.res && isRecursivePosition(df, pos);
      df <- fuse(df, dg, pos)
    )
      yield df
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
      case CannotFuse =>
        None
    }
  }

  def isConstructor(fun: Fun) = {
    // st.datatypes exists { case (_, dt) =>
    //   dt.constrs contains fun
    // }
    fun.name == "nil" || fun.name == "cons"
  }

  def isRecursivePosition(df: Def[Flat], pos: Int): Boolean = {
    df.cases exists { case Flat(args, guard, body) =>
      args(pos).isInstanceOf[App]
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
      // if the case of g is a variable only,
      // then do not take it apart according to the cases of f,
      // instead simply wrap it into f
      case Flat(gargs, gguard, x: Var) =>
        val fargs =
          for ((t, i) <- f.args.zipWithIndex)
            yield Var("x", t, Some(i))
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs updated (pos, x)
        val guard = gguard
        val body = App(f, recs)
        List(Flat(args, guard, body))

      // if the case of g is a tail-recursive call,
      // then wrap it in f which produces fg directly
      case Flat(gargs, gguard, App(`g`, _, grecs)) =>
        val fargs =
          for ((t, i) <- f.args.zipWithIndex)
            yield Var("x", t, Some(i))
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs patch (pos, grecs, 1)
        val guard = gguard
        val body = App(fg, recs)
        List(Flat(args, guard, body))

      // otherwise, we need to split up all the cases of f
      // and see which ones match
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

  // Note: this can be done by subst su and the simplifier
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
  ): List[(List[Expr], Map[Var, Expr])] =
    (pat, d) match {
      case (x: Var, _) if su contains x =>
        if (su(x) == d) {
          List((args, su))
        } else {
          // println("; cannot expose " + x + " over " + d)
          // println("; already bound to " + su(x))
          // println(fg)
          // println()
          throw CannotFuse
        }

      case (x: Var, _) =>
        List((args, su + (x -> d)))

      // constructor match: we can recurse into the arguments
      // Note: pat should only have constructors in function position
      case (App(fun1, _, pats), App(fun2, _, ds)) if isConstructor(fun2) =>
        if (fun1 == fun2) {
          expose(f, g, fg, pats, args, ds, su)
        } else {
          // println("refute exposing " + pat + " over " + d)
          Nil
        }

      // case (_, App(fun2, _, ds)) if defs contains fun2 =>
      //   println("; cannot expose " + pat + " over " + fun2)
      //   throw CannotFuse

      // unconstrained argument: we can chain the pattern to the top-level
      // TODO: later possibly remove x from the vars of the case
      case (_, x: Var) if args contains x =>
        val pos = args indexOf x
        val args_ = args updated (pos, pat)
        List((args_, su))

      case _ =>
        // println("; cannot expose " + pat + " over " + d)
        // println("; " + fg)
        // println()
        throw CannotFuse
    }

  def expose(
      f: Fun,
      g: Fun,
      fg: Fun,
      pats: List[Expr],
      args0: List[Expr],
      ds: List[Expr],
      su0: Map[Var, Expr]
  ): List[(List[Expr], Map[Var, Expr])] =
    (pats, ds) match {
      case (Nil, Nil) =>
        List((args0, su0))

      case (pat :: pats, d :: ds) =>
        for (
          (args1, su1) <- expose(f, g, fg, pat, args0, d, su0);
          (args2, su2) <- expose(f, g, fg, pats, args1, ds, su1)
        )
          yield (args2, su2)
    }
}

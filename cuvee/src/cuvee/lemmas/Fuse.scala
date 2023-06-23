package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.util.Name
import cuvee.StringOps

object Fuse {
  var debug = true

  def mayFuseAt(df: Def, dg: Def): List[Int] = {
    for (
      (typ, pos) <- df.fun.args.zipWithIndex if dg.isRecursive
      if typ == dg.fun.res && isMatchingPosition(df, pos)
    )
      yield pos
  }

  def fuseAt(
      df: Def,
      xs: List[Expr],
      dg: Def,
      ys: List[Expr],
      pos: Int,
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]]
  ): Option[(Def, List[Expr])] = {
    val Def(f, fcases) = df
    val Def(g, gcases) = dg

    require(
      f.args(pos) == g.res,
      "cannot fuse " + f + " with " + g + " at pos " + pos
    )

    val name = fused(f.name, g.name, pos)
    val params = f.params ++ g.params
    val args = f.args patch (pos, g.args, 1)
    val res = f.res
    val fg = Fun(name, params.distinct, args, res)
    println("fusing " + name)

    try {
      val cases =
        for (
          gcase <- gcases;
          flat <- fuse(f, g, fg, fcases, gcase, pos, constrs, rules)
        )
          yield flat

      val dfg = Def(fg, cases)

      // val xs =
      //   for ((t, i) <- f.args.zipWithIndex)
      //     yield Var(Name("x", Some(i)), t)
      // val ys =
      //   for ((t, i) <- g.args.zipWithIndex)
      //     yield Var(Name("y", Some(i)), t)

      // val lhs = App(f, xs updated (pos, App(g, ys)))
      // val rhs = App(, )
      // val rule = Rule(lhs, rhs, True)
      // println(" ok")
      Some((dfg, xs patch (pos, ys, 1)))
    } catch {
      case CannotFuse =>
        // println(" failed")
        None
    }
  }

  def fuse(
      f: Fun,
      g: Fun,
      fg: Fun,
      fcases: List[C],
      gcase: C,
      pos: Int,
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]]
  ): List[C] = {
    val xs = Expr.vars("x", f.args)
    val ys = Expr.vars("y", g.args)
    val lhs = App(f, xs updated (pos, App(g, ys)))
    val rhs = App(fg, xs patch (pos, ys, 1))
    val eq = Rule(lhs, rhs)

    val rules_ =
      if (rules contains f)
        rules + (f -> (eq :: rules(f)))
      else
        rules + (f -> List(eq))

    val C(gargs, gguard, gbody) = gcase

    // Note: this is *not* using the additional rule,
    // because we want to connect the *outer* occurrence of f,
    // not just any other that happens to be part of gbody,
    // as it happens for append.reverse when reverse's body
    // is defined by or normalized to append(reverse(xs), cons(x, nil))
    val gbody_ = Simplify.simplify(gbody, rules, constrs)

    val args = xs updated (pos, gbody_)
    val body = App(f, args)
    val body_ = Rewrite.app(body, f, args, rules_)
        // println("gbody:  " + gbody)
        // println("gbody_:  " + gbody_)
        // println("body:  " + body)
        // println("body_: " + body_)
        // println("args:  " + args)
        // println()

    if (isFused(f, g, body_)) {
      val args = xs patch (pos, gargs, 1)
      val guard = gguard
      // if (debug) {
      //   println("gbody:  " + gbody)
      //   println("body:  " + body)
      //   println("body_: " + body_)
      //   println("args:  " + args)
      //   println("guard: " + guard)
      //   println()
      // }
      List(C(args, guard, body_))
    } else {
      val fpats = fcases flatMap (_.args)
      val critical = gargs.free & fpats.free
      val re = Expr.fresh(critical)
      val fcases_ = fcases map (_ rename re)

      for (
        C(fargs, fguard, fbody) <- fcases_;
        (gargs_, su) <- expose(f, g, fg, fargs(pos), gargs, gbody_, constrs, rules)
      ) yield {
        val args = fargs patch (pos, gargs_, 1)
        val guard = (fguard ++ gguard) subst su
        val body_ = recurse(f, g, fg, pos, fbody, su, constrs, rules) // fbody subst su
        C(args, guard, body_)
      }
    }
  }

  def fuse_(
      f: Fun,
      g: Fun,
      fg: Fun,
      fcases: List[C],
      gcase: C,
      pos: Int,
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]]
  ): List[C] =
    gcase match {
      // if the case of g is non-recursive in g,
      // then do not take it apart according to the cases of f,
      // instead simply wrap it into f
      case C(gargs, gguard, gbody) if !(g in gbody) =>
        val fargs = Expr.vars("x", f.args)
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs updated (pos, gbody)
        val guard = gguard
        val body = App(f, recs)
        List(C(args, guard, body))

      // if the case of g is a tail-recursive call,
      // then wrap it in f which produces fg directly
      case C(gargs, gguard, App(Inst(`g`, _), grecs)) =>
        val fargs = Expr.vars("x", f.args)
        val args = fargs patch (pos, gargs, 1)
        val recs = fargs patch (pos, grecs, 1)
        val guard = gguard
        val body = App(fg, recs)
        List(C(args, guard, body))

      // otherwise, we need to split up all the cases of f
      // and see which ones match
      case C(gargs, gguard, gbody) =>
        val fpats = fcases flatMap (_.args)
        val critical = gcase.args.free & fpats.free
        val re = Expr.fresh(critical)
        val fcases_ = fcases map (_ rename re)

        for (
          C(fargs, fguard, fbody) <- fcases_;
          (gargs_, su) <- expose(f, g, fg, fargs(pos), gargs, gbody, constrs, rules)
        ) yield {
          val args = fargs patch (pos, gargs_, 1)
          val guard = (fguard subst su) ++ gguard
          val body_ = recurse(f, g, fg, pos, fbody, su, constrs, rules) // fbody subst su
          C(args, guard, body_)
        }
    }

  // g must not occur inside argument positions of f
  def isFused(f: Fun, g: Fun, e: Expr): Boolean = e match {
    case App(inst, args) if inst.fun == f =>
      !(g in args)

    case App(inst, args) =>
      args forall (isFused(f, g, _))

    case Bind(quant, formals, body, typ) =>
      isFused(f, g, body)

    case _ =>
      true
  }

  object CannotFuse extends Exception

  def isMatchingPosition(df: Def, pos: Int): Boolean = {
    df.cases exists { case C(args, guard, body) =>
      val arg = args(pos)
      arg.isInstanceOf[App] || arg.isInstanceOf[Lit]
    }
  }

  def fused(f: Name, g: Name, pos: Int) = {
    // XXX: change if we want to fuse multiple functions
    val Name(str1, None) = f
    val Name(str2, None) = g
    Name(str1 + ":" + pos + ":" + str2, None)
  }

  // collect cases of a definition that match a particular pattern
  // possibly unfolding other function definitions, too (not implemented yet);
  // make sure the variables in pat do not clash with those in the arguments of the cases!
  // this function probably works less well with normalized definitions (Split.scala)
  def expose(
      f: Fun,
      g: Fun,
      fg: Fun,
      fpat: Expr,
      gargs: List[Expr],
      gbody: Expr,
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]],
      su: Map[Var, Expr] = Map()
  ): List[(List[Expr], Map[Var, Expr])] =
    (fpat, gbody) match {
      case (x: Var, _) if su contains x =>
        if (su(x) == gbody) {
          List((gargs, su))
        } else {
          println("; cannot expose " + x + " over " + gbody)
          println("; already bound to " + su(x))
          println("; " + fg)
          println()
          throw CannotFuse
        }

      case (x: Var, _) =>
        List((gargs, su + (x -> gbody)))

      case (Lit(any1, _), Lit(any2, _)) =>
        if (any1 == any2) List((gargs, su))
        else Nil

      case (True | False, _) =>
        if (fpat == gbody) List((gargs, su))
        else Nil

      // constructor match: we can recurse into the arguments
      // Note: pat should only have constructors in function position
      case (App(inst1, fpats), App(inst2, gexprs)) if constrs contains inst2.fun =>
        if (inst1.fun == inst2.fun) {
          require(inst1 == inst2, "not implemented: fusing of polymorphic functions")
          expose(f, g, fg, fpats, gargs, gexprs, constrs, rules, su)
        } else {
          // println("refute exposing " + pat + " over " + d)
          Nil
        }

      case (Succ(fpat), Succ(gexpr)) =>
        expose(f, g, fg, fpat, gargs, gexpr, constrs, rules, su)

      // case (_, App(fun2, _, ds)) if defs contains fun2 =>
      //   println("; cannot expose " + pat + " over " + fun2)
      //   throw CannotFuse

      // unconstrained argument: we can chain the pattern to the top-level
      // TODO: later possibly remove x from the vars of the case
      case (_, x: Var) if gargs contains x =>
        val pos = gargs indexOf x
        println(
          "instantiating unconstrained argument " + x + " at " + pos + " of " + g.name + " with " + fpat
        )
        // TODO: clarify when this can happen!!
        ???
        val args_ = gargs updated (pos, fpat)
        List((args_, su))

      case _ =>
        val gbody_ = Simplify.simplify(gbody, rules, constrs)
        if (gbody_ != gbody) {
          if (debug)
            println("simplified " + gbody + " to " + gbody_)
          expose(f, g, fg, fpat, gargs, gbody_, constrs, rules, su)
        } else {
          if (debug)
            println("cannot expose " + fpat + " over " + gbody + " for " + fg)
          throw CannotFuse
        }

      // case _ =>
      //   println("cannot expose " + fpat + " over " + gbody + " for " + fg)
      //   throw CannotFuse
    }

  def expose(
      f: Fun,
      g: Fun,
      fg: Fun,
      pats: List[Expr],
      args0: List[Expr],
      exprs: List[Expr],
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]],
      su0: Map[Var, Expr]
  ): List[(List[Expr], Map[Var, Expr])] =
    (pats, exprs) match {
      case (Nil, Nil) =>
        List((args0, su0))

      case (pat :: pats, first :: rest) =>
        for (
          (args1, su1) <- expose(f, g, fg, pat, args0, first, constrs, rules, su0);
          (args2, su2) <- expose(f, g, fg, pats, args1, rest, constrs, rules, su1)
        )
          yield (args2, su2)
    }

  // Note: this can be done by subst su and the simplifier
  def recurse(
      f: Fun,
      g: Fun,
      fg: Fun,
      pos: Int,
      body: Expr,
      su: Map[Var, Expr],
      constrs: Set[Fun],
      rules: Map[Fun, List[Rule]]
  ): Expr =
    body match {
      case x: Var if su contains x =>
        su(x) // non-recursive matched case
      case x: Var =>
        x
      case l: Lit =>
        l
      case App(Inst(`f`, _), args) =>
        val args_ = args map (recurse(f, g, fg, pos, _, su, constrs, rules))
        args_(pos) match {
          case App(Inst(`g`, _), args) =>
            val res = App(fg, args_ patch (pos, args, 1))
            res
          // case App(_, args) if g in args =>
          //   val expr = App(f, args_)
          //   println("not in fused form for " + fg + ": " + expr)
          //   expr
          //   throw CannotFuse
          case _ =>
            val expr = App(f, args_)
            val expr_ = Simplify.simplify(expr, rules, constrs)
            if (expr != expr_) {
              if (debug)
                println("simplified " + expr + " to " + expr_)
              recurse(f, g, fg, pos, expr_, su, constrs, rules)
            } else if (isFused(f, g, expr_)) {
              expr_
            } else {
              if (debug)
                println("not in fused form for " + fg + ": " + expr_)
              throw CannotFuse
            }
        }
      case App(h, args) =>
        val args_ = args map (recurse(f, g, fg, pos, _, su, constrs, rules))
        App(h, args_)
    }

}

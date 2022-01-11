package cuvee.pure

import cuvee.sexpr.Syntax

case class Rule(lhs: Expr, rhs: Expr, cond: Expr) extends Syntax {
  val vars = lhs.free.toList

  val toExpr =
    (vars, cond) match {
      case (Nil, True) => Eq(lhs, rhs)
      case (_, True)   => Forall(vars, Eq(lhs, rhs))
      case (Nil, _)    => Imp(cond, Eq(lhs, rhs))
      case _           => Forall(vars, Imp(cond, Eq(lhs, rhs)))
    }

  def sexpr = toExpr.sexpr
  override def toString = toExpr.toString
}

object Rewrite {
  def rewrite(expr: Expr, rules: Map[Fun, List[Rule]]): Expr = {
    expr bottomup {
      case App(fun, _, args) =>
        app(expr, fun, args, rules)

      case _ =>
        expr
    }
  }

  def rewrite(exprs: List[Expr], rules: Map[Fun, List[Rule]]): List[Expr] = {
    exprs map (rewrite(_, rules))
  }

  def app(
      expr: Expr,
      fun: Fun,
      args: List[Expr],
      rules: Map[Fun, List[Rule]]
  ): Expr = {
    if (rules contains fun) {
      val _expr = app(expr, rules(fun), rules)
      _expr
    } else {
      expr
    }
  }

  def app(expr: Expr, todo: List[Rule], rules: Map[Fun, List[Rule]]): Expr = {
    todo match {
      case Nil =>
        expr

      case Rule(pat, rhs, cond) :: rest =>
        bind(pat, expr, Map[Var, Expr]()) match {
          case None =>
            app(expr, rest, rules)
          case Some(env) =>
            val _cond = cond // simplify(cond subst env, ctx, st)
            if (_cond == True)
              rewrite(rhs subst env, rules)
            else
              app(expr, rest, rules)
        }
    }
  }

  def bind(
      pats: List[Expr],
      args: List[Expr],
      env0: Map[Var, Expr]
  ): Option[Map[Var, Expr]] = {
    (pats, args) match {
      case (Nil, Nil) =>
        Some(env0)
      case (pat :: pats, arg :: args) =>
        for (
          env1 <- bind(pat, arg, env0);
          env2 <- bind(pats, args, env1)
        ) yield env2
      case _ =>
        None
    }
  }

  def bind(
      pat: Expr,
      arg: Expr,
      env: Map[Var, Expr] = Map()
  ): Option[Map[Var, Expr]] = {
    (pat, arg) match {
      case (x: Var, _) if !(env contains x) =>
        Some(env + (x -> arg))
      case (x: Var, _) if (env contains x) && (env(x) == arg) =>
        Some(env)
      case (x: Var, _) =>
        None
      case (a: Lit, b: Lit) if a == b =>
        Some(env)
      case (App(fun1, inst1, pats), App(fun2, inst2, args)) if fun1 == fun2 =>
        bind(pats, args, env)
      case _ =>
        // println("cannot bind " + pat + " to " + arg + " in " + env)
        None
    }
  }

  def matches(
      pat: Expr,
      arg: Expr,
      env: Map[Var, Expr] = Map()
  ): Boolean = {
    bind(pat, arg, env) match {
      case None    => false
      case Some(_) => true
    }
  }
}

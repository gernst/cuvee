package cuvee.imp

import cuvee.pure._

case class Path(
    fresh: List[Var],
    constraints: List[Expr],
    vars: List[Map[Var, Expr]],
    old: List[List[Map[Var, Expr]]]
) {
  def constraint = {
    And(constraints)
  }

  def pushOld = {
    copy(old = vars :: old)
  }

  def popOld = {
    copy(old = old.tail)
  }

  def lookup(x: Var) = {
    Path.lookup(vars, x)
  }

  def eval(expr: Expr) = {
    Path.eval(vars, old, expr)
  }

  def eval(exprs: List[Expr]) = {
    Path.eval(vars, old, exprs)
  }

  def local(xs: List[Var], rhs: List[Expr]) = {
    require(rhs.isEmpty || xs.length == rhs.length)

    if (rhs.nonEmpty) {
      val rhs_ = Path.eval(vars, old, rhs)
      val su = Expr.subst(xs, rhs_)
      copy(vars = su :: vars)
    } else {
      val su = Expr.fresh(xs)
      val xs_ = xs rename su
      val fresh_ = fresh ++ xs_
      val vars_ = su :: vars
      Path(fresh_, constraints, vars_, old)
    }
  }

  def assign(xs: List[Var], rhs: List[Expr]) = {
    require(xs.length == rhs.length)
    val rhs_ = Path.eval(vars, old, rhs)
    val vars_ = (xs zip rhs_).foldLeft(vars)(Path.store)
    Path(fresh, constraints, vars_, old)
  }

  def spec(xs: List[Var], pre: Expr, post: Expr) = {
    val su = Expr.fresh(xs)
    val xs_ = xs rename su
    val pre_ = Path.eval(vars, old, pre)
    val post_ = Path.eval(su :: vars, vars :: old, pre)

    // Note, assume instead of assert pre_ here
    // because we aim to construct a path with all constraints that
    // are known to hold if execution passes on
    val fresh_ = fresh ++ xs_
    val constraints_ = post_ :: pre_ :: constraints
    val vars_ = su :: vars
    Path(fresh_, constraints_, vars_, old)
  }
}

object Path {
  // delegate all operations on paths to ensure we don't
  // accidentally re-use the top-level versions of vars and olds
  def eval(vars: List[Map[Var, Expr]], old: List[List[Map[Var, Expr]]], expr: Expr): Expr = {
    expr match {
      case x: Var =>
        lookup(vars, x)

      case _: Lit =>
        expr

      case Is(arg, fun) =>
        Is(eval(vars, old, arg), fun)

      case Note(expr, attr) =>
        Note(eval(vars, old, expr), attr)

      case App(inst, args) =>
        App(inst, eval(vars, old, args))

      case Distinct(args) =>
        Distinct(eval(vars, old, args))

      case Old(expr) =>
        require(old.nonEmpty, "cannot evaluate old expression, no previous state(s) given")
        val vars_ :: old_ = old
        eval(vars_, old_, expr)

      case Bind(quant, formals, body, typ) =>
        val su = Expr.id(formals)
        val body_ = eval(su :: vars, old, body)
        Bind(quant, formals, body_, typ)
    }
  }

  def eval(
      vars: List[Map[Var, Expr]],
      old: List[List[Map[Var, Expr]]],
      exprs: List[Expr]
  ): List[Expr] = {
    for (expr <- exprs)
      yield eval(vars, old, expr)
  }

  def lookup(vars: List[Map[Var, Expr]], x: Var): Expr = {
    vars match {
      case Nil =>
        cuvee.error("unbound local variable: " + x)

      case st :: outer if st contains x =>
        st(x)

      case st :: outer =>
        lookup(outer, x)
    }
  }

  def store(vars: List[Map[Var, Expr]], xe: (Var, Expr)): List[Map[Var, Expr]] = {
    val (x, e) = xe

    vars match {
      case Nil =>
        cuvee.error("unbound local variable: " + x)

      case st :: outer if st contains x =>
        val st_ = st + xe
        st_ :: outer

      case st :: outer =>
        st :: store(outer, xe)
    }
  }
}

package cuvee.imp

import cuvee.pure._

case class Path(
    fresh: List[Var],
    constraints: List[Expr],
    stack: List[Map[Var, Expr]],
    old: List[List[Map[Var, Expr]]]
) {
  def constraint = {
    And(constraints)
  }

  def pushOld = {
    copy(old = stack :: old)
  }

  def popOld = {
    copy(old = old.tail)
  }

  def pushScope = {
    copy(stack = Map[Var, Expr]() :: stack)
  }

  def popScope = {
    copy(stack = stack.tail)
  }

  def lookup(x: Var) = {
    Path.lookup(stack, x)
  }

  def eval(expr: Expr) = {
    Path.eval(stack, old, expr)
  }

  def eval(exprs: List[Expr]) = {
    Path.eval(stack, old, exprs)
  }

  def local(xs: List[Var], rhs: List[Expr]) = {
    require(rhs.isEmpty || xs.length == rhs.length)

    val top :: rest = stack

    if (rhs.nonEmpty) {
      val rhs_ = Path.eval(stack, old, rhs)
      val su = Expr.subst(xs, rhs_)
      val stack_ = (top ++ su) :: rest
      Path(fresh, constraints, stack_, old)
    } else {
      val su = Expr.fresh(xs)
      val xs_ = xs rename su
      val fresh_ = fresh ++ xs_
      val stack_ = (top ++ su) :: rest
      Path(fresh_, constraints, stack_, old)
    }
  }

  def assign(xs: List[Var], rhs: List[Expr]) = {
    require(xs.length == rhs.length)
    val rhs_ = Path.eval(stack, old, rhs)
    val stack_ = Path.store(stack, xs zip rhs_)
    Path(fresh, constraints, stack_, old)
  }

  def assume(phi: Expr) = {
    val phi_ = Path.eval(stack, old, phi)
    val constraints_ = phi_ :: constraints
    Path(fresh, constraints_, stack, old)
  }

  def step(xs: List[Var], rel: Expr) = {
    val su = Expr.fresh(xs)
    val xs_ = xs rename su
    val rel_ = Path.eval(su :: stack, stack :: old, rel)

    val fresh_ = fresh ++ xs_
    val constraints_ = rel_ :: constraints
    val stack_ = Path.store(stack, xs zip xs_)
    Path(fresh_, constraints_, stack_, old)
  }
}

object Path {
  // delegate all operations on paths to ensure we don't
  // accidentally re-use the top-level versions of stack and olds
  def eval(stack: List[Map[Var, Expr]], old: List[List[Map[Var, Expr]]], expr: Expr): Expr = {
    expr match {
      case x: Var =>
        lookup(stack, x)

      case _: Lit =>
        expr

      case Is(arg, fun) =>
        Is(eval(stack, old, arg), fun)

      case Note(expr, attr) =>
        Note(eval(stack, old, expr), attr)

      case App(inst, args) =>
        App(inst, eval(stack, old, args))

      case Distinct(args) =>
        Distinct(eval(stack, old, args))

      case Old(expr) =>
        require(old.nonEmpty, "cannot evaluate old expression, no previous state(s) given")
        val stack_ :: old_ = old
        eval(stack_, old_, expr)

      case Bind(quant, formals, body, typ) =>
        val su = Expr.id(formals)
        val body_ = eval(su :: stack, old, body)
        Bind(quant, formals, body_, typ)
    }
  }

  def eval(
      stack: List[Map[Var, Expr]],
      old: List[List[Map[Var, Expr]]],
      exprs: List[Expr]
  ): List[Expr] = {
    for (expr <- exprs)
      yield eval(stack, old, expr)
  }

  def lookup(stack: List[Map[Var, Expr]], x: Var): Expr = {
    stack match {
      case Nil =>
        cuvee.error("unbound local variable: " + x)

      case st :: outer if st contains x =>
        st(x)

      case st :: outer =>
        lookup(outer, x)
    }
  }

  def store(stack: List[Map[Var, Expr]], eqs: List[(Var, Expr)]): List[Map[Var, Expr]] = {
    eqs.foldLeft(stack)(store)
  }

  def store(stack: List[Map[Var, Expr]], xe: (Var, Expr)): List[Map[Var, Expr]] = {
    val (x, e) = xe

    stack match {
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

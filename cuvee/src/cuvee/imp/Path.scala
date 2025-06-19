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
    Path.lookup(fresh, stack, x)
  }

  def lookup(xs: List[Var]) = {
    xs map { Path.lookup(fresh, stack, _) }
  }

  def eval(expr: Expr) = {
    Path.eval(fresh, stack, old, expr)
  }

  def eval(exprs: List[Expr]) = {
    Path.eval(fresh, stack, old, exprs)
  }

  def local(xs: List[Var], rhs: List[Expr]) = {
    require(rhs.isEmpty || xs.length == rhs.length)

    val top :: rest = stack

    if (rhs.nonEmpty) {
      val rhs_ = Path.eval(fresh, stack, old, rhs)
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
    val rhs_ = Path.eval(fresh, stack, old, rhs)
    val stack_ = Path.store(stack, xs zip rhs_)
    Path(fresh, constraints, stack_, old)
  }

  def assume(phi: Expr) = {
    val phi_ = Path.eval(fresh, stack, old, phi)
    val constraints_ = And.flattenStrong(phi_) ++ constraints
    Path(fresh, constraints_, stack, old)
  }

  def step(xs: List[Var], rel: Expr) = {
    val su = Expr.fresh(xs)
    val xs_ = xs rename su
    // println()
    // println("evaluating:")
    // println(rel)
    // println(fresh)
    // println(su)
    // println(stack)
    // println()

    val rel_ = Path.eval(fresh, su :: stack, stack :: old, rel)
    val fresh_ = fresh ++ xs_
    val constraints_ = And.flattenStrong(rel_) ++ constraints
    val stack_ = Path.store(stack, xs zip xs_)
    Path(fresh_, constraints_, stack_, old)
  }
}

object Path {
  case object Unbound extends Exception

  // delegate all operations on paths to ensure we don't
  // accidentally re-use the top-level versions of stack and olds
  def eval(
      bound: List[Var],
      stack: List[Map[Var, Expr]],
      old: List[List[Map[Var, Expr]]],
      expr: Expr
  ): Expr = {
    // println("evaluating: " + expr)
    expr match {
      case x: Var =>
        try {
          lookup(bound, stack, x)
        } catch {
          case Unbound =>
            // println("bound:      " + bound)
            // println("stack:      " + stack)
            // println("old:        " + old)
            // println()
            cuvee.error("unbound variable: " + x + " in " + stack.flatMap(_.keySet).mkString(", "))
        }

      case _: Lit =>
        expr

      case Is(arg, fun) =>
        Is(eval(bound, stack, old, arg), fun)

      case Note(expr, patterns, attr) =>
        Note(eval(bound, stack, old, expr), patterns map (eval(bound, stack, old, _)), attr)

      case App(inst, args) =>
        App(inst, eval(bound, stack, old, args))

      case Distinct(args) =>
        Distinct(eval(bound, stack, old, args))

      case Old(expr) =>
        require(old.nonEmpty, "cannot evaluate old expression, no previous state(s) given")
        val stack_ :: old_ = old
        eval(bound, stack_, old_, expr)

      case expr @ Bind(quant, formals, body, typ) =>
        val su = Expr.id(formals)
        val body_ = eval(bound ++ formals, stack, old, body)
        Bind(quant, formals, body_, typ)

      // XXX: stuff from loop summary approximated with subst
      case expr: Extra =>
        val su = stack.reduceRight(_ ++ _)
        expr subst su
    }
  }

  def eval(
      formals: List[Var],
      stack: List[Map[Var, Expr]],
      old: List[List[Map[Var, Expr]]],
      exprs: List[Expr]
  ): List[Expr] = {
    for (expr <- exprs)
      yield eval(formals, stack, old, expr)
  }

  def lookup(bound: List[Var], stack: List[Map[Var, Expr]], x: Var): Expr = {
    stack match {
      case Nil if bound contains x =>
        x

      case Nil =>
        throw Unbound
      // cuvee.error("unbound local variable: " + x)

      case st :: outer if st contains x =>
        st(x)

      case st :: outer =>
        lookup(bound, outer, x)
    }
  }

  def store(stack: List[Map[Var, Expr]], eqs: List[(Var, Expr)]): List[Map[Var, Expr]] = {
    // println("storing: " + eqs)
    // println("stack: " + stack)
    // require(eqs.nonEmpty, "why store nothing?")
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

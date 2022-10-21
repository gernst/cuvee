package cuvee.pure

import cuvee.sexpr.Syntax
import cuvee.smtlib.Assert
import cuvee.State
import cuvee.util.Name

case class Rule(
    lhs: Expr,
    rhs: Expr,
    cond: Expr = True,
    avoid: List[(Expr, Expr)] = Nil
) extends Syntax {
  require(
    lhs.typ == rhs.typ && cond.typ == Sort.bool,
    "rule " + this + " not type correct: " + lhs.typ + ", " + rhs.typ
  )

  val vars = lhs.free.toList

  def canFlip = rhs match {
    case _: App =>
      lhs.free subsetOf rhs.free
    case _ =>
      false
  }

  def flip = {
    require(canFlip, "cannot flip rule: " + this)
    Rule(rhs, lhs, cond, avoid)
  }

  def maybeFlip = {
    if (canFlip)
      Some(Rule(rhs, lhs, cond, avoid))
    else
      None
  }

  def fun = {
    val App(inst, _) = lhs
    inst.fun
  }

  val toExpr =
    (vars, cond) match {
      case (Nil, True) => Eq(lhs, rhs)
      case (_, True)   => Forall(vars, Eq(lhs, rhs))
      case (Nil, _)    => Imp(cond, Eq(lhs, rhs))
      case _           => Forall(vars, Imp(cond, Eq(lhs, rhs)))
    }

  def sexpr = toExpr

  def cmd = Assert(toExpr)

  override def toString = {
    var res = lhs + " = " + rhs
    var pres = And.flatten(cond)
    pres ++= avoid map { case (x, e) => (x !== e) }

    if (pres.nonEmpty)
      res += " if " + And(pres)

    res
  }
}

object Rule {
  def from(
      xs: List[Var],
      guard: Expr,
      inst: Inst,
      args: List[Expr],
      x: Var,
      pat: Expr,
      body: Expr,
      st: State
  ): List[Rule] = {
    val su = Map(x -> pat)
    val _args = args subst su
    val _lhs = App(inst, _args)
    from(xs ++ pat.free, guard, _lhs, body, st)
  }

  def from(
      xs: List[Var],
      guard: Expr,
      lhs: App,
      rhs: Expr,
      st: State
  ): List[Rule] =
    rhs match {
      case Ite(test, left, right) =>
        val l = from(xs, test && guard, lhs, left, st)
        val r = from(xs, Not(test) && guard, lhs, right, st)
        l ++ r

      // boolean right-hand sides are taken apart according to short-cut semantics
      case Or(List(test, expr)) => // TODO: generalize
        val l = from(xs, test && guard, lhs, True, st)
        val r = from(xs, Not(test) && guard, lhs, expr, st)
        l ++ r

      case And(List(test, expr)) => // TODO: generalize
        val l = from(xs, test && guard, lhs, expr, st)
        val r = from(xs, Not(test) && guard, lhs, False, st)
        l ++ r

      // case matches can only be decomposed if they are over an unconstrained variable argument,
      //   f(x) = match x with ...
      // but not when the match is against an arbitrary expressions
      //   f(x) = match e with ...
      // (the latter could be made possible for by unification wrt. constructors for some cases)
      case Match(x: Var, cases, typ) if xs contains x =>
        for (
          Case(pat, body) <- cases;
          res <- from(xs, guard, lhs.inst, lhs.args, x, pat, body, st)
        )
          yield res

      case _ =>
        List(Rule(lhs, rhs, guard))
    }

  def from(
      name: Name,
      xs: List[Var],
      body: Expr,
      st: State
  ): List[Rule] = {
    val fun = st funs (name, xs.length)
    val lhs = App(fun, xs)
    from(xs, True, lhs, body, st)
  }

  def from(
      xs: List[Var],
      guard: Expr,
      suc: Expr,
      st: State
  ): List[Rule] =
    suc match {
      case Eq(lhs: App, rhs) =>
        from(xs, guard, lhs, rhs, st)
      case Not(lhs: Bind) =>
        Nil
      case Not(lhs: App) =>
        from(xs, guard, lhs, False, st)
      case lhs: App =>
        from(xs, guard, lhs, True, st)
      case _ =>
        Nil
    }

  def from(expr: Expr, st: State): List[Rule] = {
    val Clause(xs, ant, suc) = expr
    from(xs, And(ant), suc, st)
  }

  def from(exprs: List[Expr], st: State): List[Rule] = {
    for (
      expr <- exprs;
      rule <- from(expr, st)
    )
      yield rule
  }

}

package cuvee.pure

import cuvee.util.Syntax
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

  // require(
  //   rhs.free subsetOf lhs.free,
  //   "rule " + this + " does not bind " + (rhs.free -- lhs.free) + " in rhs " + rhs
  // )

  // require(
  //   cond.free subsetOf lhs.free,
  //   "rule " + this + " does not bind " + (cond.free -- lhs.free) + " in guard " + cond
  // )

  val vars = lhs.free.toList
  def funs = lhs.funs ++ rhs.funs ++ cond.funs

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
    var pres = And.flattenStrong(cond)
    pres ++= avoid map { case (x, e) => (x !== e) }

    if (pres.nonEmpty)
      res += " if " + And(pres)

    res
  }
}

object Rules {
  var ite = true
  var shortcut = true

  def from(
      xs: List[Var],
      guard: Expr,
      inst: Inst,
      args: List[Expr],
      x: Var,
      pat: Expr,
      body: Expr,
      ok: Set[Fun]
  ): List[Rule] = {
    val su = Map(x -> pat)
    val _args = args subst su
    val _lhs = App(inst, _args)
    from(xs ++ pat.free, guard, _lhs, body, ok)
  }

  def from(
      xs: List[Var],
      guard: Expr,
      lhs: App,
      rhs: Expr,
      ok: Set[Fun]
  ): List[Rule] =
    rhs match {
      case _ if !(ok contains lhs.fun) =>
        Nil

      case Ite(test, left, right) if ite =>
        val l = from(xs, test && guard, lhs, left, ok)
        val r = from(xs, Not(test) && guard, lhs, right, ok)
        l ++ r

      // boolean right-hand sides are taken apart according to short-cut semantics
      case Or(List(test, expr)) if shortcut => // TODO: generalize
        val l = from(xs, test && guard, lhs, True, ok)
        val r = from(xs, Not(test) && guard, lhs, expr, ok)
        l ++ r

      case Or(List(test1, test2, expr)) if shortcut => // TODO: generalize
        val a = from(xs, test1 && guard, lhs, True, ok)
        val b = from(xs, Not(test1) && test2 && guard, lhs, expr, ok)
        val c = from(xs, Not(test1) && Not(test2) && guard, lhs, expr, ok)
        a ++ b ++ c

      case And(List(test, expr)) if shortcut => // TODO: generalize
        val l = from(xs, test && guard, lhs, expr, ok)
        val r = from(xs, Not(test) && guard, lhs, False, ok)
        l ++ r

      // case matches can only be decomposed if they are over an unconstrained variable argument,
      //   f(x) = match x with ...
      // but not when the match is against an arbitrary expressions
      //   f(x) = match e with ...
      // (the latter could be made possible for by unification wrt. constructors for some cases)
      case Match(x: Var, cases, typ) if xs contains x =>
        for (
          Case(pat, body) <- cases;
          res <- from(xs, guard, lhs.inst, lhs.args, x, pat, body, ok)
        )
          yield res

      case _ if guard.free subsetOf lhs.free =>
        List(Rule(lhs, rhs, guard))

      case _ =>
        Nil
    }

  def from(
      fun: Fun,
      xs: List[Var],
      body: Expr,
      ok: Set[Fun]
  ): List[Rule] = {
    val lhs = App(fun, xs)
    from(xs, True, lhs, body, ok)
  }

  def from(
      xs: List[Var],
      guard: Expr,
      suc: Expr,
      ok: Set[Fun]
  ): List[Rule] =
    suc match {
      case Eq(lhs: App, rhs) =>
        from(xs, guard, lhs, rhs, ok)
      // case Not(lhs: Bind) =>
      //   Nil
      case Not(lhs: App) =>
        from(xs, guard, lhs, False, ok)
      case lhs: App =>
        from(xs, guard, lhs, True, ok)
      case _ =>
        Nil
    }

  def from(expr: Expr, ok: Set[Fun]): List[Rule] = {
    val Clause(xs, ant, suc) = expr.stripNotes
    from(xs, And(ant), suc, ok)
  }

  def from(exprs: List[Expr], ok: Set[Fun]): List[Rule] = {
    for (
      expr <- And.flatten(exprs);
      rule <- from(expr, ok)
    )
      yield rule
  }
}

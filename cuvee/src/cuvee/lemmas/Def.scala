package cuvee.lemmas

import cuvee.pure._

sealed trait Case {
  def args: List[Expr]
  def guard: List[Expr]
  def typ: Type
  def prime: Case

  def free = args.free
}

case class Flat(args: List[Expr], guard: List[Expr], body: Expr) extends Case {
  def typ = body.typ

  def prime = {
    val re = Expr.subst(free map (x => (x, x.prime)))
    Flat(args rename re, guard rename re, body rename re)
  }
}

case class Norm(
    args: List[Expr],
    guard: List[Expr],
    as: Map[Var, Expr],
    bs: Map[Var, List[Expr]],
    cs: Map[Var, Expr],
    d: Expr
) extends Case {
  def typ = d.typ
  def isBaseCase = bs.isEmpty

  def prime = {
    val re = Expr.subst(free map (x => (x, x.prime)))
    val as_ = as map { case (a, e) => (a, e rename re) }
    val bs_ = bs map { case (b, e) => (b, e rename re) }
    val cs_ = cs map { case (c, e) => (c, e rename re) }

    Norm(
      args rename re,
      guard rename re,
      as_,
      bs_,
      cs_,
      d rename re
    )
  }
}

case class Def[+C <: Case](fun: Fun, cases: List[C]) {
  for (cs <- cases) {
    require(
      fun.args == cs.args.types,
      "type mismatch: " + fun + " applied to " + cs.args
    )
    require(fun.res == cs.typ, "type mismatch: " + fun + " in case " + cs)
  }

  def prime = {
    Def(fun, cases map (_.prime.asInstanceOf[C]))
  }
}

object Def {
  def rw(
      xs: List[Var],
      guard: List[Expr],
      lhs: App,
      rhs: Expr,
      st: State
  ): List[(Fun, Flat)] =
    (lhs, rhs) match {
      case (App(fun, _, args), Ite(test, left, right)) =>
        val l = rw(xs, test :: guard, lhs, left, st)
        val r = rw(xs, Not(test) :: guard, lhs, right, st)
        l ++ r

      case (App(fun, _, args), rhs) =>
        List((fun, Flat(args, guard, rhs)))

      case _ =>
        Nil
    }

  def rw(expr: Expr, st: State): List[(Fun, Flat)] =
    expr match {
      case Clause(xs, ant, Eq(lhs: App, rhs)) =>
        rw(xs, ant, lhs, rhs, st)

      case _ =>
        Nil
    }

  def rw(exprs: List[Expr], st: State): List[(Fun, Flat)] = {
    for (
      expr <- exprs;
      rule <- rw(expr, st)
    )
      yield rule
  }
}

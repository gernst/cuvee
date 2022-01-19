package cuvee.lemmas

import cuvee.pure._
import cuvee.smtlib._

trait Case {
  def args: List[Expr]
  def guard: List[Expr]
  def typ: Type
  def free = args.free
  def rename(re: Map[Var, Var]): Case
  def rule(self: Fun): Rule
  def flat(self: Fun): Flat
  def axiom(self: Fun): Expr
}

case class Flat(args: List[Expr], guard: List[Expr], body: Expr) extends Case {
  def typ = body.typ
  def flat(self: Fun) = this

  def rename(re: Map[Var, Var]) = {
    Flat(args rename re, guard rename re, body rename re)
  }

  def rule(self: Fun): Rule = {
    Rule(App(self, args), body, And(guard))
  }
  def axiom(self: Fun) = {
    val xs = args.free.toList
    Clause(xs, guard, Eq(App(self, args), body))
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

  def rename(re: Map[Var, Var]) = {
    Norm(
      args rename re,
      guard rename re,
      as map { case (a, e) => (a, e rename re) },
      bs map { case (b, e) => (b, e rename re) },
      cs map { case (c, e) => (c, e rename re) },
      d rename re
    )
  }

  def body(self: Fun) = {
    val bs_ = bs map { case (b, args) =>
      b -> App(self, args subst as)
    }

    d subst (bs_ ++ cs)
  }

  def flat(self: Fun) = {
    Flat(args, guard, body(self))
  }

  def rule(self: Fun) = {
    Rule(App(self, args), body(self), And(guard))
  }

  def axiom(self: Fun) = {
    val xs = args.free.toList
    Clause(xs, guard, Eq(App(self, args), body(self)))
  }
}

case class Def[+C <: Case](fun: Fun, cases: List[C]) {
  for (cs <- cases) {
    require(
      fun.args == cs.args.types,
      "type mismatch: " + fun + " applied to " + cs.args
    )
    require(
      fun.res == cs.typ,
      "type mismatch: " + fun + " in case " + cs + ": " + cs.typ
    )
  }

  def decl = {
    val Fun(name, Nil, args, res) = fun
    DeclareFun(name, args, res)
  }

  def axioms = {
    cases map (cs => Assert(cs axiom fun))
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

package cuvee.lemmas

import cuvee.pure._
import cuvee.smtlib._

trait CS {
  def args: List[Expr]
  def guard: List[Expr]
  def typ: Type
  def free = args.free
  def rename(re: Map[Var, Var]): CS
  def rule(self: Fun): Rule
  def flat(self: Fun): Flat
  def axiom(self: Fun): Expr
}

case class Flat(args: List[Expr], guard: List[Expr], body: Expr) extends CS {
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
) extends CS {
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

case class Def[+C <: CS](fun: Fun, cases: List[C]) {
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
    DeclareFun(name.toString, args, res)
  }

  def axioms = {
    cases map (cs => Assert(cs axiom fun))
  }
}

object Def {
  def rw(
      xs: List[Var],
      guard: List[Expr],
      fun: Inst,
      args: List[Expr],
      x: Var,
      pat: Expr,
      body: Expr,
      st: State
  ): List[(Fun, Flat)] = {
    val su = Map(x -> pat)
    val _args = args subst su
    val _lhs = App(fun, _args)
    rw(xs ++ pat.free, guard, _lhs, body, st)
  }

  def rw(
      xs: List[Var],
      guard: List[Expr],
      lhs: App,
      rhs: Expr,
      st: State
  ): List[(Fun, Flat)] =
    (lhs, rhs) match {
      case (_, Ite(test, left, right)) =>
        val l = rw(xs, test :: guard, lhs, left, st)
        val r = rw(xs, Not(test) :: guard, lhs, right, st)
        l ++ r

      case (App(fun, args), Match(x: Var, cases, typ)) if xs contains x =>
        // val pos = args indexOf x
        for (
          Case(pat, body) <- cases;
          res <- rw(xs, guard, fun, args, x, pat, body, st)
        )
          yield res

      case (App(inst, args), Match(x, cases, typ)) =>
        println("cannot lift match statement: " + rhs)
        println(lhs)
        ???

      case (App(inst, args), rhs) =>
        List((inst.fun, Flat(args, guard, rhs)))

      case _ =>
        Nil
    }

  def rw(
      name: String,
      xs: List[Var],
      res: Type,
      body: Expr,
      st: State
  ): List[(Fun, Flat)] = {
    val fun = st funs name
    val lhs = App(fun, xs)
    rw(xs, Nil, lhs, body, st)
  }

  def rw(expr: Expr, st: State): List[(Fun, Flat)] =
    expr match {
      case Clause(xs, ant, Eq(lhs: App, rhs)) =>
        rw(xs, ant, lhs, rhs, st)

      case Clause(xs, ant, Not(lhs: Bind)) =>
        Nil

      case Clause(xs, ant, Not(lhs: App)) =>
        rw(xs, ant, lhs, False, st)

      case Clause(xs, ant, lhs: App) =>
        rw(xs, ant, lhs, True, st)

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

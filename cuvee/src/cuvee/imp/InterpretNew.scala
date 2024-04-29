package cuvee.imp

import cuvee.pure._

object Interpret {
  case class Path(
      fresh: List[Var],
      constraints: List[Expr],
      vars: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ) {
    def assign(xs: List[Var], rhs: List[Expr]) = {
      copy(vars = vars ++ (xs zip rhs))
    }
  }

  trait Symbolic extends Interpret[Path] {
    def eval(state: Path, expr: Expr) =
      expr subst state.vars

    def spec(states: List[Path], xs: List[Var], pre: Expr, post: Expr): List[Path] = {
      val re = Expr.fresh(xs)
      val xs_ = xs rename re

      for (Path(fresh, constraints, vars, old) <- states)
        yield ???
    }

    def local(states: List[Path], xs: List[Var], rhs: List[Expr]): List[Path] = {
      val re = Expr.fresh(xs)
      val xs_ = xs rename re

      for (Path(fresh, constraints, vars, old) <- states)
        yield ???
    }

    def assign(states: List[Path], xs: List[Var], rhs: List[Expr]): List[Path] = {
      for (path <- states)
        yield path assign (xs, rhs map (eval(path, _)))
    }
  }

  trait WithFixpoint[S] {
    this: Interpret[S] =>
    def isSubsetOf(states1: List[S], states2: List[S]): Boolean
    def widen(states1: List[S], states2: List[S]): List[S]
    def narrow(states1: List[S], states2: List[S]): List[S]

    def fixpoint(init: List[S], fuel: Int = 5)(next: List[S] => List[S]): List[S] = {
      require(fuel >= 0, "too many iterations in fixpoint")

      val states = next(init)

      if (isSubsetOf(states, init))
        states
      else
        fixpoint(states, fuel - 1)(next)
    }

    def iter(
        states0: List[S],
        test: Expr,
        body: Prog
    ): List[S] = {
      val widened = fixpoint(states0) { states =>
        val states1 = exec(assume(states0, test), body)
        val result = widen(states0, states1)
        result
      }

      val narrowed = fixpoint(widened) { states =>
        val states1 = exec(assume(states0, test), body)
        val result = narrow(states0, states1)
        result
      }

      narrowed
    }

    def while_(
        states0: List[S],
        test: Expr,
        body: Prog,
        term: Expr,
        inv: Expr,
        sum: Expr,
        frames: List[Frame]
    ): List[S] = {
      assume(iter(states0, test, body), !test)
    }
  }
}

trait Interpret[S] {
  def while_(
      states0: List[S],
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): List[S]

  def spec(states: List[S], xs: List[Var], pre: Expr, post: Expr): List[S]
  def local(states: List[S], xs: List[Var], rhs: List[Expr]): List[S]
  def assign(states: List[S], xs: List[Var], rhs: List[Expr]): List[S]

  // Note: default implementations

  def join(states1: List[S], states2: List[S]): List[S] = {
    states1 ++ states2
  }

  def assume(states: List[S], pre: Expr): List[S] = {
    spec(states, Nil, pre, True)
  }

  def assert(states: List[S], post: Expr): List[S] = {
    spec(states, Nil, True, post)
  }

  def block(states: List[S], progs: List[Prog]): List[S] = {
    progs.foldLeft(states)(exec)
  }

  def if_(states0: List[S], test: Expr, left: Prog, right: Prog): List[S] = {
    val states1 = exec(assume(states0, test), left)
    val states2 = exec(assume(states0, !test), right)
    join(states1, states2)
  }

  def exec(states: List[S], prog: Prog): List[S] = prog match {
    case Block(progs) =>
      block(states, progs)

    case Local(xs, rhs) =>
      local(states, xs, rhs)

    case Assign(xs, rhs) =>
      assign(states, xs, rhs)

    case Spec(xs, pre, post) =>
      spec(states, xs, pre, post)

    case If(test, left, right) =>
      if_(states, test, left, right)

    case While(test, body, term, inv, sum, frames) =>
      while_(states, test, body, term, inv, sum, frames)
  }
}

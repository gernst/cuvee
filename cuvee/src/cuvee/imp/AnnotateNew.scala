package cuvee.imp

import cuvee.pure._

abstract class Annotate[S](val interpret: Interpret[S]) {
  def while_(
      states: List[S],
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (List[S], Prog)

  // Note: default implementations

  def spec(states: List[S], xs: List[Var], pre: Expr, post: Expr): (List[S], Prog) = {
    (interpret.spec(states, xs, pre, post), Spec(xs, pre, post))
  }

  def local(states: List[S], xs: List[Var], rhs: List[Expr]): (List[S], Prog) = {
    (interpret.local(states, xs, rhs), Local(xs, rhs))
  }

  def assign(states: List[S], xs: List[Var], rhs: List[Expr]): (List[S], Prog) = {
    (interpret.assign(states, xs, rhs), Assign(xs, rhs))
  }

  // def join(states1: List[S], states2: List[S]): List[S]
  // def widen(states1: List[S], states2: List[S]): List[S]

  def block(states0: List[S], progs: List[Prog]): (List[S], List[Prog]) = progs match {
    case Nil =>
      (states0, Nil)

    case (prog: Prog) :: (rest: List[Prog]) =>
      val (states1, prog_) = annotate(states0, prog)
      val (states2, rest_) = block(states1, rest)
      (states2, prog_ :: rest_)
  }

  def if_(states0: List[S], test: Expr, left: Prog, right: Prog): (List[S], Prog) = {
    import interpret.assume
    import interpret.join

    val (states1, left_) = annotate(assume(states0, test), left)
    val (states2, right_) = annotate(assume(states0, !test), right)
    (join(states1, states2), If(test, left_, right_))
  }

  def annotate(states: List[S], prog: Prog): (List[S], Prog) = prog match {
    case Block(progs) =>
      val (states_, progs_) = block(states, progs)
      (states_, Block(progs_))

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

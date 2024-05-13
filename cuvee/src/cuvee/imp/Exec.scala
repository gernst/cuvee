package cuvee.imp

import cuvee.pure._

case class States[S](
    running: List[S],
    breaked: List[S] = Nil,
    returned: List[S] = Nil,
    asserted: List[(S, Expr)] = Nil
) {
  def break = {
    States(Nil, breaked ++ running, returned, asserted)
  }

  def unbreak = {
    States(running ++ breaked, Nil, returned, asserted)
  }

  def return_ = {
    States(Nil, breaked, returned ++ running, asserted)
  }

  def run(f: List[S] => List[S]) = {
    States(f(running), breaked, returned, asserted)
  }

  def assert(phi: Expr) = {
    val asserted_ = running map (_ -> phi)
    States(running, breaked, returned, asserted ++ asserted_)
  }

  def merge(that: States[S])(f: (List[S], List[S]) => List[S]) = {
    States(
      f(this.running, that.running),
      this.breaked ++ that.breaked,
      this.returned ++ that.returned,
      this.asserted ++ that.asserted
    )
  }
}

trait Exec[S] {
  def entry(in: List[Var], out: List[Var], spec: Option[Spec]): List[S]
  def assume(states: List[S], phi: Expr): List[S]
  def step(states: List[S], xs: List[Var], rel: Expr): List[S]
  def local(states: List[S], xs: List[Var], rhs: List[Expr]): List[S]
  def assign(states: List[S], xs: List[Var], rhs: List[Expr]): List[S]
  def scoped(states: List[S])(f: List[S] => List[S]): List[S]

  // Note: default implementations

  def break(states: States[S]) =
    states.break

  def return_(states: States[S]) =
    states.return_

  def assume(states: States[S], phi: Expr): States[S] =
    states run { assume(_, phi) }

  def assert(states: States[S], phi: Expr): States[S] =
    states assert phi

  def local(states: States[S], xs: List[Var], rhs: List[Expr]): States[S] =
    states run { local(_, xs, rhs) }

  def assign(states: States[S], xs: List[Var], rhs: List[Expr]): States[S] =
    states run { assign(_, xs, rhs) }

  def spec(states: States[S], xs: List[Var], pre: Expr, post: Expr): States[S] = {
    assert(states, pre) run { step(_, xs, post) }
  }

  def scoped(states: States[S])(f: States[S] => States[S]): States[S] = {
    ???
  }

  def join(states1: States[S], states2: States[S]) = {
    (states1 merge states2)(_ ++ _)
  }

  def block(states0: States[S], progs: List[Prog]): States[S] = {
    progs match {
      case Nil =>
        states0

      case prog :: rest =>
        val states1 = exec(states0, prog)
        val states2 = block(states1, rest)
        states2
    }
  }

  def if_(states0: States[S], test: Expr, left: Prog, right: Prog): States[S] = {
    val states1 = exec(assume(states0, test), left)
    val states2 = exec(assume(states0, !test), right)
    join(states1, states2)
  }

  def while_(
      states0: States[S],
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): States[S]

  def exec(states: States[S], prog: Prog): States[S] = prog match {
    case Break =>
      break(states)

    case Return =>
      return_(states)

    case Block(progs) =>
      scoped(states) { block(_, progs) }

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

object Exec {
  // TODO: de-duplicate this with the domain-based interpreter
  trait WithPath {
    def entry(in: List[Var], out: List[Var], spec: Option[Spec]) =
      spec match {
        case None =>
          val su = Expr.id(in ++ out)
          val fresh = Nil
          val constraints = Nil
          val vars = List(su)
          val init = Path(fresh, constraints, vars, List(vars))
          List(init)

        case Some(Spec(globals, pre, post)) =>
          val su = Expr.id(in ++ out ++ globals)
          val fresh = Nil
          val constraints = List(pre)
          val vars = List(su)
          val init = Path(fresh, constraints, vars, List(vars))
          List(init)
      }

    def local(states: List[Path], xs: List[Var], rhs: List[Expr]) =
      for (path <- states)
        yield path.local(xs, rhs)

    def assign(states: List[Path], xs: List[Var], rhs: List[Expr]) =
      for (path <- states)
        yield path.assign(xs, rhs)

    def assume(states: List[Path], phi: Expr): List[Path] =
      for (path <- states)
        yield path.assume(phi)

    def step(states: List[Path], xs: List[Var], rel: Expr): List[Path] =
      for (path <- states)
        yield path.step(xs, rel)

    def withOld(states0: List[Path])(f: List[Path] => List[Path]) = {
      val states1 = states0 map (_.pushOld)
      val states2 = f(states1)
      val states3 = states2 map (_.popOld)
      states3
    }

    def scoped(states0: List[Path])(f: List[Path] => List[Path]) = {
      val states1 = states0 map (_.pushScope)
      val states2 = f(states1)
      val states3 = states2 map (_.popScope)
      states3
    }
  }

  trait WithFixpoint[S] {
    this: Exec[S] =>

    def isSubsetOf(states1: List[S], states2: List[S]): Boolean
    def widen(states1: List[S], states2: List[S]): List[S]
    def narrow(states1: List[S], states2: List[S]): List[S]

    // it is probably good enough to compare the running states,
    // which are the ones from which we had executed the loop already
    def isSubsetOf(states1: States[S], states2: States[S]): Boolean =
      isSubsetOf(states1.running, states2.running)

    def widen(states1: States[S], states2: States[S]): States[S] =
      (states1 merge states2)(widen)

    def narrow(states1: States[S], states2: States[S]): States[S] =
      (states1 merge states2)(narrow)

    def fixpoint(init: States[S], fuel: Int = 5)(next: States[S] => States[S]): States[S] = {
      require(fuel >= 0, "too many iterations in fixpoint")

      val states = next(init)

      if (isSubsetOf(states, init))
        states
      else
        fixpoint(states, fuel - 1)(next)
    }

    def iter(
        states0: States[S],
        test: Expr,
        body: Prog
    ): States[S] = {
      val widened = fixpoint(states0) { states0 =>
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
        states0: States[S],
        test: Expr,
        body: Prog,
        term: Expr,
        inv: Expr,
        sum: Expr,
        frames: List[Frame]
    ): States[S] = {
      val states1 = iter(states0, test, body)
      val states2 = assume(states1, !test)
      states2.unbreak
    }
  }
}

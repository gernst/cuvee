package cuvee.imp

import cuvee.pure._

class Exec2[V, S](val sem: Sem[V, S]) {
  case class Path(vars: Map[Var, V], state: S)

  case class Paths(
      running: List[Path],
      breaked: List[Path] = Nil,
      returned: List[Path] = Nil,
      asserted: List[(Path, Expr)] = Nil
  )

  object Paths {
    val arbitrary = {
      val init = Path(Map(), sem.arbitrary)
      Paths(List(init))
    }
  }

  def merge(paths1: Paths, paths2: Paths)(f: (List[Path], List[Path]) => List[Path]): Paths = {
    Paths(
      f(paths1.running, paths2.running),
      paths1.breaked ++ paths2.breaked,
      paths1.returned ++ paths2.returned,
      paths1.asserted ++ paths2.asserted
    )
  }

  def break_(paths: Paths): Paths = {
    import paths._
    Paths(Nil, breaked ++ running, returned, asserted)
  }

  def return_(paths: Paths): Paths = {
    import paths._
    Paths(Nil, breaked, returned ++ running, asserted)
  }

  def assume(paths: Paths, phi: Expr): Paths = {
    import paths._

    val running_ =
      for (
        Path(vars, state) <- running;
        state_ <- sem.assume(vars, state, phi)
      )
        yield Path(vars, state_)

    Paths(running_, breaked, returned, asserted)
  }

  def local(paths: Paths, xs: List[Var], rhs: List[Expr]): Paths = {
    import paths._

    val running_ =
      for (
        Path(vars, state) <- running;
        (vs, state_) = sem.local(vars, state, xs, rhs)
      )
        yield Path(vars ++ (xs zip vs), state_)

    Paths(running_, breaked, returned, asserted)
  }

  def assign(paths: Paths, xs: List[Var], rhs: List[Expr]): Paths = {
    import paths._

    val running_ =
      for (
        Path(vars, state) <- running;
        state_ = sem.assign(vars, state, xs, rhs)
      )
        yield Path(vars, state_)

    Paths(running_, breaked, returned, asserted)
  }

  def spec(paths: Paths, xs: List[Var], pre: Expr, post: Expr): Paths = {
    import paths._

    val asserted_ =
      for (path @ Path(vars, state) <- running)
        yield (path, pre)

    val running_ =
      for (
        Path(vars, state) <- running;
        state_ <- sem.step(vars, state, xs, post)
      )
        yield Path(vars, state_)

    Paths(running_, breaked, returned, asserted ++ asserted_)
  }

  def forget(paths: Paths, xs: Set[Var]): Paths = {
    import paths._

    val running_ =
      for (
        Path(vars, state) <- running;
        state_ = sem.forget(vars, state, xs)
      )
        yield Path(vars, state_)

    Paths(running_, breaked, returned, asserted)
  }

  def join(paths1: Paths, paths2: Paths): Paths = {
    merge(paths1, paths2)(_ ++ _)
  }

  def exec(
      scope: List[Set[Var]],
      paths: Paths,
      progs: List[Prog],
      conts: List[List[Prog]],
      old: List[Paths]
  ): Paths = {
    progs match {
      case Nil =>
        (scope, conts) match {
          case (Nil, Nil) =>
            paths
          case (locals :: scope, progs :: cont) =>
            exec(scope, forget(paths, locals), progs, cont, old)
        }

      case Block(progs) :: rest =>
        val top: Set[Var] = Set()
        exec(top :: scope, paths, progs, rest :: conts, old)

      case Local(xs, rhs) :: rest =>
        local(paths, xs, rhs)

      case Assign(xs, rhs) :: rest =>
        assign(paths, xs, rhs)

      case Spec(xs, pre, post) :: rest =>
        spec(paths, xs, pre, post)

      case Break :: rest =>
        break_(paths)

      case Return :: rest =>
        return_(paths)

      case If(test, left, right) :: rest =>
        val paths1 = exec(scope, assume(paths, test), left :: progs, conts, old)
        val paths2 = exec(scope, assume(paths, !test), right :: progs, conts, old)
        join(paths1, paths2)
    }
  }
}

package cuvee.imp

import cuvee.pure._
import cuvee.ai.Domain
import cuvee.State

case class Paths(
    running: List[Path],
    breaked: List[Path] = Nil,
    returned: List[Path] = Nil,
    asserted: List[(Path, Expr)] = Nil
)

object ExecNoLoops extends Exec {
  def while_(
      paths0: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): Paths = {
    cuvee.error("execution of loops not implemented in this context")
  }
}

class ExecWithDomain[S](domain: Domain[S]) extends Exec {
  def while_(
      paths0: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): Paths = {
    cuvee.error("execution of loops not implemented in this context")
  }
}

trait Exec {
  // The only requirement is that the resulting final paths
  // overapproximate the effect of executing the loop.
  def while_(
      paths0: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): Paths

  // Utility function to run an arbitrary iteration of a loop body,
  // when started from paths, with respect to the set of vars given,
  // starting out with a *flat* stack of the identity substitution,
  // i.e., not reflecting the block structure of the given current paths.
  def iter(
      state: State,
      paths: Paths,
      vars: List[Var],
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (Paths, Paths) = {
    val scope = List(vars)

    val su = Expr.id(vars)
    val fresh = Nil
    val constraints = List(test, inv)
    val stack = List(su)

    val init = Path(fresh, constraints, stack, List(stack))
    val before = Paths(List(init))
    val after = exec(state, before, body)

    (before, after)
  }

  def entry(vars: List[Var], constraints: List[Expr]): Paths = {
    val su = Expr.id(vars)
    val fresh = Nil
    val stack = List(su)
    val init = Path(fresh, constraints, stack, List(stack))
    Paths(List(init))
  }

  def entry(in: List[Var], out: List[Var], spec: Option[Spec]): Paths =
    spec match {
      case None =>
        entry(in ++ out, Nil)

      case Some(Spec(globals, pre, post)) =>
        entry(in ++ out ++ globals, List(pre))
    }

  def break(paths: Paths) = {
    import paths._
    Paths(Nil, breaked ++ running, returned, asserted)
  }

  def resume(paths: Paths) = {
    import paths._
    Paths(running ++ breaked, Nil, returned, asserted)
  }

  def return_(paths: Paths) = {
    import paths._
    Paths(Nil, breaked, returned ++ running, asserted)
  }

  def assume(paths: Paths, phi: Expr): Paths = {
    import paths._
    val running_ = running map { _ assume phi }
    Paths(running_, breaked, returned, asserted)
  }

  def assert(paths: Paths, phi: Expr): Paths = {
    import paths._
    val asserted_ = running map { (_, phi) }
    Paths(running, breaked, returned, asserted ++ asserted_)
  }

  def local(paths: Paths, xs: List[Var], rhs: List[Expr]): Paths = {
    import paths._
    val running_ = running map { _ local (xs, rhs) }
    Paths(running_, breaked, returned, asserted)
  }

  def assign(paths: Paths, xs: List[Var], rhs: List[Expr]): Paths = {
    import paths._
    val running_ = running map { _ assign (xs, rhs) }
    Paths(running_, breaked, returned, asserted)
  }

  def spec(paths: Paths, xs: List[Var], pre: Expr, post: Expr): Paths = {
    import paths._
    val asserted_ = running map { (_, pre) }
    val running_ = running map { _ step (xs, post) }
    Paths(running_, breaked, returned, asserted ++ asserted_)
  }

  def scoped(paths0: Paths)(f: Paths => Paths): Paths = {
    val paths1 = all(paths0) { _.pushScope }
    val paths2 = f(paths1)
    val paths3 = all(paths2) { _.popScope }
    paths3
  }

  // def withOld(paths0: Paths)(f: Paths => Paths): Paths = {
  //   val paths1 = all(paths0) { _.pushOld }
  //   val paths2 = f(paths1)
  //   val paths3 = all(paths2) { _.popOld }
  //   paths3
  // }

  def all(paths: Paths)(f: Path => Path) = {
    import paths._
    val running_ = running map f
    val breaked_ = breaked map f
    val returned_ = returned map f
    val asserted_ = asserted map { case (path, phi) => (f(path), phi) }
    Paths(running_, breaked_, returned_, asserted_)
  }

  def join(paths1: Paths, paths2: Paths) = {
    val Paths(running1, breaked1, returned1, asserted1) = paths1
    val Paths(running2, breaked2, returned2, asserted2) = paths2

    Paths(
      running1 ++ running2,
      breaked1 ++ breaked2,
      returned1 ++ returned2,
      asserted1 ++ asserted2
    )
  }

  def block(state: State, paths0: Paths, progs: List[Prog]): Paths = {
    progs match {
      case Nil =>
        paths0

      case prog :: rest =>
        val paths1 = exec(state, paths0, prog)
        val paths2 = block(state, paths1, rest)
        paths2
    }
  }

  def if_(
      state: State,
      paths0: Paths,
      test: Expr,
      left: Prog,
      right: Prog
  ): Paths = {
    val paths1 = exec(state, assume(paths0, test), left)
    val paths2 = exec(state, assume(paths0, !test), right)
    join(paths1, paths2)
  }

  def exec(state: State, paths: Paths, prog: Prog): Paths = prog match {
    case Break =>
      break(paths)

    case Return =>
      return_(paths)

    case Local(xs, rhs) =>
      local(paths, xs, rhs)

    case Assign(xs, rhs) =>
      assign(paths, xs, rhs)

    case Spec(xs, pre, post) =>
      spec(paths, xs, pre, post)

    case Block(progs) =>
      scoped(paths) {
        block(state, _, progs)
      }

    case If(test, left, right) =>
      if_(state, paths, test, left, right)

    case While(test, body, term, inv, sum, frames) =>
      resume {
        while_(paths, test, body, term, inv, sum, frames)
      }
  }
}

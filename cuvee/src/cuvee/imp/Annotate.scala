package cuvee.imp

import cuvee.pure._
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.DefineProc

abstract class Annotate extends Stage {
  def exec: Exec

  def exec(
      prefix: List[Cmd],
      cmds: List[Cmd],
      last: Cmd,
      state: cuvee.State
  ) = {
    cmds flatMap {
      case DefineProc(name, params, in, out, spec, body) =>
        val paths = Paths(exec.entry(in, out, spec))
        val (paths_, body_) = annotate(paths, body)
        List(DefineProc(name, params, in, out, spec, body_))

      case cmd =>
        List(cmd)
    }
  }

  def while_(
      paths: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (Paths, Prog)

  // Note: default implementations

  def break_(paths: Paths) =
    (exec.break(paths), Break)

  def return_(paths: Paths) =
    (exec.return_(paths), Return)

  def spec(paths: Paths, xs: List[Var], pre: Expr, post: Expr) =
    (exec.spec(paths, xs, pre, post), Spec(xs, pre, post))

  def local(paths: Paths, xs: List[Var], rhs: List[Expr]) =
    (exec.local(paths, xs, rhs), Local(xs, rhs))

  def assign(paths: Paths, xs: List[Var], rhs: List[Expr]) =
    (exec.assign(paths, xs, rhs), Assign(xs, rhs))

  def block(paths0: Paths, progs: List[Prog]): (Paths, List[Prog]) = progs match {
    case Nil =>
      (paths0, Nil)

    case (prog: Prog) :: (rest: List[Prog]) =>
      val (paths1, prog_) = annotate(paths0, prog)
      val (paths2, rest_) = block(paths1, rest)
      (paths2, prog_ :: rest_)
  }

  def if_(paths0: Paths, test: Expr, left: Prog, right: Prog): (Paths, Prog) = {
    val (paths1, left_) = annotate(exec.assume(paths0, test), left)
    val (paths2, right_) = annotate(exec.assume(paths0, !test), right)
    (exec.join(paths1, paths2), If(test, left_, right_))
  }

  def annotate(paths: Paths, prog: Prog): (Paths, Prog) = prog match {
    case Break =>
      break_(paths)

    case Return =>
      return_(paths)

    case Block(progs) =>
      val (paths_, progs_) = block(paths, progs)
      (paths_, Block(progs_))

    case Local(xs, rhs) =>
      local(paths, xs, rhs)

    case Assign(xs, rhs) =>
      assign(paths, xs, rhs)

    case Spec(xs, pre, post) =>
      spec(paths, xs, pre, post)

    case If(test, left, right) =>
      if_(paths, test, left, right)

    case While(test, body, term, inv, sum, frames) =>
      while_(paths, test, body, term, inv, sum, frames)
  }
}

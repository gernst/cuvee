package cuvee.imp

import cuvee.pure._
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.DefineProc
import cuvee.State

abstract class Annotate(val exec: Exec) extends Stage {
  def exec(
      prefix: List[Cmd],
      cmds: List[Cmd],
      last: Cmd,
      state: State
  ) = {
    cmds flatMap {
      case DefineProc(name, params, in, out, spec, body) =>
        val paths = exec.entry(in, out, spec)
        val (cmds_, paths_, body_) = annotate(state, paths, body)
        cmds_ ++ List(DefineProc(name, params, in, out, spec, body_))

      case cmd =>
        List(cmd)
    }
  }

  // The only requirement is that the resulting final paths
  // overapproximate the effect of executing the loop,
  // and that the updated program overapproximates the loop too,
  // e.g. by additional candidate invariants.
  def while_(
      state: State,
      paths: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (List[Cmd], Paths, Prog)

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
  ): (List[Cmd], Paths, Paths, Prog) = {
    val scope = List(vars)

    val su = Expr.id(vars)
    val fresh = Nil
    val constraints = And.flattenStrong(test && inv)
    val stack = List(su)

    val init = Path(fresh, constraints, stack, List(stack))
    val before = Paths(List(init))
    val (cmds, after, body_) = annotate(state, before, body)

    (cmds, before, after, body_)
  }

  def entry(state: State, vars: List[Var], constraints: List[Expr]): Paths = {
    exec.entry(vars, constraints)
  }

  def break_(state: State, paths: Paths): (List[Cmd], Paths, Prog) =
    (Nil, exec.break(paths), Break)

  def return_(state: State, paths: Paths): (List[Cmd], Paths, Prog) =
    (Nil, exec.return_(paths), Return)

  def resume(stuff: (List[Cmd], Paths, Prog)): (List[Cmd], Paths, Prog) = {
    val (cmds, paths, prog) = stuff
    (cmds, exec.resume(paths), prog)
  }

  def spec(
      state: State,
      paths: Paths,
      xs: List[Var],
      pre: Expr,
      post: Expr
  ): (List[Cmd], Paths, Prog) = {
    (Nil, exec.spec(paths, xs, pre, post), Spec(xs, pre, post))
  }

  def local(state: State, paths: Paths, xs: List[Var], rhs: List[Expr]): (List[Cmd], Paths, Prog) =
    (Nil, exec.local(paths, xs, rhs), Local(xs, rhs))

  def assign(state: State, paths: Paths, xs: List[Var], rhs: List[Expr]): (List[Cmd], Paths, Prog) =
    (Nil, exec.assign(paths, xs, rhs), Assign(xs, rhs))

  def call(
      state: State,
      paths: Paths,
      name: cuvee.util.Name,
      in: List[Expr],
      out: List[Var]
  ): (List[Cmd], Paths, Prog) = {
    (Nil, exec.call(state, paths, name, in, out), Call(name, in, out))
  }

  def block(
      state: State,
      paths0: Paths,
      progs: List[Prog]
  ): (List[Cmd], Paths, List[Prog]) = progs match {
    case Nil =>
      (Nil, paths0, Nil)

    case (prog: Prog) :: (rest: List[Prog]) =>
      val (cmds1, paths1, prog_) = annotate(state, paths0, prog)
      val (cmds2, paths2, rest_) = block(state, paths1, rest)
      (cmds1 ++ cmds2, paths2, prog_ :: rest_)
  }

  def if_(
      state: State,
      paths0: Paths,
      test: Expr,
      left: Prog,
      right: Prog
  ): (List[Cmd], Paths, Prog) = {
    val (cmds1, paths1, left_) = annotate(state, exec.assume(paths0, test), left)
    val (cmds2, paths2, right_) = annotate(state, exec.assume(paths0, !test), right)
    (cmds1 ++ cmds2, exec.join(paths1, paths2), If(test, left_, right_))
  }

  def annotate(state: State, paths: Paths, prog: Prog): (List[Cmd], Paths, Prog) = {
    prog match {
      case Break =>
        break_(state, paths)

      case Return =>
        return_(state, paths)

      case Block(progs) =>
        val (cmds_, paths_, progs_) = block(state, paths, progs)
        (cmds_, paths_, Block(progs_))

      case Local(xs, rhs) =>
        local(state, paths, xs, rhs)

      case Assign(xs, rhs) =>
        assign(state, paths, xs, rhs)

      case Spec(xs, pre, post) =>
        spec(state, paths, xs, pre, post)

      case Call(name, in, out) =>
        call(state, paths, name, in, out)

      case If(test, left, right) =>
        if_(state, paths, test, left, right)

      case While(test, body, term, inv, sum, frames) =>
        // body match {
        //   case Block(progs_) if progs_.exists(e => e.isInstanceOf[While]) =>
        //     cuvee.error("annotating nested loops is not supported.")

        //   case _ =>
        resume {
          while_(state, paths, test, body, term, inv, sum, frames)
        }
      // }
    }
  }
}

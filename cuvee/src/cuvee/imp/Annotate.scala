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
        val (paths_, body_) = annotate(state, paths, body)
        List(DefineProc(name, params, in, out, spec, body_))

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
  ): (Paths, Prog)

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
  ): (Paths, Paths, Prog) = {
    val scope = List(vars)

    val su = Expr.id(vars)
    val fresh = Nil
    val constraints = List(test, inv)
    val stack = List(su)

    val init = Path(fresh, constraints, stack, List(stack))
    val before = Paths(List(init))
    val (after, body_) = annotate(state, before, body)

    (before, after, body_)
  }

  def break_(paths: Paths) =
    (exec.break(paths), Break)

  def return_(paths: Paths) =
    (exec.return_(paths), Return)

  def resume(stuff: (Paths, Prog)) = {
    val (paths, prog) = stuff
    (exec.resume(paths), prog)
  }

  def spec(paths: Paths, xs: List[Var], pre: Expr, post: Expr) = {
    (exec.spec(paths, xs, pre, post), Spec(xs, pre, post))
  }

  def local(paths: Paths, xs: List[Var], rhs: List[Expr]) =
    (exec.local(paths, xs, rhs), Local(xs, rhs))

  def assign(paths: Paths, xs: List[Var], rhs: List[Expr]) =
    (exec.assign(paths, xs, rhs), Assign(xs, rhs))

  def block(
      state: State,
      paths0: Paths,
      progs: List[Prog]
  ): (Paths, List[Prog]) = progs match {
    case Nil =>
      (paths0, Nil)

    case (prog: Prog) :: (rest: List[Prog]) =>
      val (paths1, prog_) = annotate(state, paths0, prog)
      val (paths2, rest_) = block(state, paths1, rest)
      (paths2, prog_ :: rest_)
  }

  def call(
      state: State,
      paths: Paths,
      name: cuvee.util.Name,
      in: List[Expr],
      out: List[Var]
  ): (Paths, Prog) = {
    require(state.procs contains name, "unknown procedure: " + name)

    val Proc(_, params, xs, zs, spec) = state procs name

    spec match {
      case None | Some(Spec(_, True, True)) if state.procdefs contains name =>
        // intentionally mirrors variables xs, ys, as procdef may refer to
        // different vars than procdecl
        val (xs, zs, body) = state procdefs name
        val re = Expr.subst(zs, out)
        val body_ = body replace re
        val block = Block(List(Local(xs, in), Spec.havoc(out), body_))
        annotate(state, paths, block)

      case None =>
        cuvee.error(
          "inlining procedures not implemented, consider adding a contract to: "
            + name
        )

      case Some(Spec(mod, phi, psi)) =>
        val su = Expr.subst(xs, in)
        val re = Expr.subst(zs, out)
        val spec_ = Spec(mod, phi subst su, psi subst (su ++ re))
        annotate(state, paths, spec_)
    }
  }

  def if_(
      state: State,
      paths0: Paths,
      test: Expr,
      left: Prog,
      right: Prog
  ): (Paths, Prog) = {
    val (paths1, left_) = annotate(state, exec.assume(paths0, test), left)
    val (paths2, right_) = annotate(state, exec.assume(paths0, !test), right)
    (exec.join(paths1, paths2), If(test, left_, right_))
  }

  def annotate(state: State, paths: Paths, prog: Prog): (Paths, Prog) =
    prog match {
      case Break =>
        break_(paths)

      case Return =>
        return_(paths)

      case Block(progs) =>
        val (paths_, progs_) = block(state, paths, progs)
        (paths_, Block(progs_))

      case Local(xs, rhs) =>
        local(paths, xs, rhs)

      case Assign(xs, rhs) =>
        assign(paths, xs, rhs)

      case Spec(xs, pre, post) =>
        spec(paths, xs, pre, post)

      case Call(name, in, out) =>
        call(state, paths, name, in, out)

      case If(test, left, right) =>
        if_(state, paths, test, left, right)

      case While(test, body, term, inv, sum, frames) =>
        body match {
          case Block(List(While(_, _, _, _, _, _))) =>
            cuvee.error("Nested loops are not supported.")
          case _ =>
            resume {
              while_(state, paths, test, body, term, inv, sum, frames)
            }
        }
    }
}

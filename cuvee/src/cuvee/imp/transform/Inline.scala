package cuvee.imp.transform

import cuvee.util.Name
import cuvee.State
import cuvee.pure._
import cuvee.imp._

object Inline {
  def inline(state: State, name: Name, in: List[Expr], out: List[Var]): Prog = {
    require(state.procdefs contains name, "cannot inline procedure without definition: " + name)

    val (params, xs, zs, body) = state procdefs name
    val re = Expr.subst(zs, out)
    val body_ = body replace re
    val block = Block(List(Local(xs, in), Spec.havoc(out), body_))

    block
  }

  def inline(state: State, prog: Prog): Prog =
    prog match {
      case Call(name, in, out) =>
        inline(state, name, in, out)

      case Block(progs) =>
        val progs_ =
          for (prog <- progs)
            yield inline(state, prog)
        Block(progs_)

      case If(test, left, right) =>
        val left_ = inline(state, left)
        val right_ = inline(state, right)
        If(test, left_, right_)

      case While(test, body, term, inv, sum, frames) =>
        val body_ = inline(state, body)
        While(test, body_, term, inv, sum, frames)

      // Atomic: cannot contain calls
      case prog =>
        prog
    }
}

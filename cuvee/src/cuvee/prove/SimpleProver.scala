package cuvee.prove

import cuvee.pure._
import cuvee.smtlib._
import cuvee.State

class SimpleProver(solver: Solver) extends Prover {
  def exec(cmd: Cmd, state: State) {
    solver.exec(cmd, state)
  }

  def reduce(prop: Prop, state: State): Prop = {
    val expr = prop.toExpr
    Prop.from(reduce(expr))
  }

  def reduce(expr: Expr): Expr = expr match {
    case And(phis) =>
      Simplify.and(phis map reduce)

    case Imp(phi, psi) =>
      solver.scoped {
        solver.assert(phi)
        val psi_ = reduce(psi)
        Simplify.imp(phi, psi_)
      }

    case Forall(xs, body) =>
      solver.scoped {
        val re = Expr.fresh(xs)
        val re_ = re map (_.swap)

        val xs_ = xs rename re
        val body_ = body rename re

        for (Var(name, typ) <- xs_) {
          val cmd = DeclareFun(name, Nil, Nil, typ)
          solver.ack(cmd)
        }

        val body__ = reduce(body_)

        Forall(xs, body__ rename re_)
      }

    case _ if solver.isTrue(expr) =>
      True

    case _ =>
      expr
  }
}

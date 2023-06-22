package cuvee.backend

import cuvee.pure._
import cuvee.smtlib._

class SimpleProver(solver: Solver) extends Prover {
  def prove(prop: Prop): Prop = {
    val expr = prop.toExpr
    Disj.from(prove(expr))
  }

  def prove(expr: Expr): Expr = expr match {
    case And(phis) =>
      Simplify.and(phis map prove)

    case Imp(phi, psi) =>
      solver.scoped {
        solver.assert(phi)
        val psi_ = prove(psi)
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
          solver.declare(cmd)
        }

        val body__ = prove(body_)

        Forall(xs, body__ rename re_)
      }

    case _ if solver.isTrue(expr) =>
      True

    case _ =>
      expr
  }
}

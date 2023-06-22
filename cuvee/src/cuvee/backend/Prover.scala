package cuvee.backend

import cuvee.smtlib.Solver
import cuvee.pure.Prop

trait Prover {
  def reduce(prop: Prop): Prop;
}

object Prover {
  class fromSolver(solver: Solver) {
    ???
  }
}
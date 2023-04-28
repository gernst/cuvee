package cuvee.backend

import cuvee.pure.Prop

trait Prover {
  def prove(prop: Prop): Prop;
}

object Prover {
  class fromSolver(solver: Solver) {
    ???
  }
}
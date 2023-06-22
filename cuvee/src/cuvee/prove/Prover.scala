package cuvee.prove

import cuvee.smtlib.Solver
import cuvee.pure.Prop
import cuvee.State

trait Prover {
  def reduce(prop: Prop, state: State): Prop
}

object Prover {
  object dummy extends Prover {
     def reduce(prop: Prop, state: State) = prop
  }
}
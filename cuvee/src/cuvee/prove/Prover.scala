package cuvee.prove

import cuvee.smtlib.Solver
import cuvee.pure.Prop
import cuvee.State
import cuvee.smtlib.Cmd
import cuvee.pure.Atom

trait Prover {
  def exec(cmd: Cmd)
  def reduce(prop: Prop, state: State): Prop
}

object Prover {
  object dummy extends Prover {
    def exec(cmd: Cmd) {}
    def reduce(prop: Prop, state: State) = prop
  }

  def fromSolver(solver: Solver) = new Prover {
    def exec(cmd: Cmd) { solver.ack(cmd) }
    def reduce(prop: Prop, state: State) = {
      val phi = prop.toExpr
      // print("proving " + phi)
      if (solver.isTrue(phi)) {
        // println("success!")
        Atom.t
      } else {
        // println("unknown.")
        prop
      }
    }
  }
}

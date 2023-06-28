package cuvee.prove

import cuvee.smtlib.Solver
import cuvee.pure.Prop
import cuvee.State
import cuvee.smtlib.Cmd
import cuvee.pure.Atom
import cuvee.util.Counter
import cuvee.pipe.Sink
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.smtlib.Assert
import cuvee.smtlib.CheckSat

trait Prover {
  def exec(cmd: Cmd, state: State)
  def reduce(prop: Prop, state: State): Prop
}

object Prover {
  object dummy extends Prover {
    def exec(cmd: Cmd, state: State) {}
    def reduce(prop: Prop, state: State) = prop
  }

  def fromSolver(solver: Solver, useInduction: Boolean = false) = new Prover {
    def exec(cmd: Cmd, state: State) {
      solver.exec(cmd, state)
    }

    def reduce(prop: Prop, state: State) = {
      val phi = prop.toExpr
      // print("proving " + phi)
      if (solver.isTrue(phi)) {
        // println("success!")
        Atom.t
      } else if(useInduction && InductiveProver.holdsByInduction(solver, phi, state.datatypes)) {
        Atom.t
      } else {
        // println("unknown.")
        prop
      }
    }
  }

  def dump(prefix: String) = new Prover with Counter {
    import scala.collection.mutable.ListBuffer
    import cuvee.smtlib.printer

    val prelude = ListBuffer[Cmd]()

    def exec(cmd: Cmd, state: State) {
      prelude += cmd
    }

    def reduce(prop: Prop, state: State) = {
      val file = prefix + next + ".smt2"
      val stream = new PrintStream(new FileOutputStream(file))
      val sink = new Sink.print(stream)

      for (cmd <- prelude)
        sink.exec(cmd, null)

      val goal = !prop.toExpr
      sink.exec(Assert(goal), null)
      sink.exec(CheckSat, null)

      prop
    }
  }
}

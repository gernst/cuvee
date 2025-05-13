package cuvee.prove

import cuvee.smtlib.Solver
import cuvee.State
import cuvee.smtlib.Cmd
import cuvee.util.Counter
import cuvee.pipe.Sink
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.smtlib.Assert
import cuvee.smtlib.CheckSat
import cuvee.pure.Simplify
import cuvee.pure.Rewrite
import cuvee.pure.Expr
import cuvee.pure.True

trait Prover extends Tactic {
  def exec(cmd: Cmd, state: State)
  def reduce(expr: Expr, state: State): Expr
  def apply(state: State, expr: Expr) = List((expr, None))
}

object Prover {
  object dummy extends Prover {
    def exec(cmd: Cmd, state: State) {}
    def reduce(expr: Expr, state: State) = {
      expr
    }
  }

  val fromSimplifier = new Prover {
    var cmds: List[Cmd] = Nil
    def exec(cmd: Cmd, state: State) {
      // XXX: does not consider push/pop
      cmds = cmd :: cmds
    }

    def reduce(expr: Expr, state: State) = {
      val constrs = state.constrs
      val rules = Rewrite.from(cmds, state) // add some new rewrite rules
      // println("safe rules:")
      // for (rule <- rules)
      //   println("  " + rule)
      val rws = rules.groupBy(_.fun)
      val prop_ = Simplify.simplify(expr, rws, constrs)
      prop_
    }
  }

  def fromSolver(solver: Solver, useInduction: Boolean = false) = new Prover {
    def exec(cmd: Cmd, state: State) {
      solver.exec(cmd, state)
    }

    def reduce(expr: Expr, state: State) = {
      val phi = expr
      // print("proving " + phi.toString)
      if (solver.isTrue(phi)) {
        // println("success!")
        True
      } else if (useInduction && InductiveProver.holdsByInduction(solver, phi, state.datatypes)) {
        True
      } else {
        // println("unknown.")
        expr
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

    def reduce(prop: Expr, state: State) = {
      val file = prefix + next + ".smt2"
      val stream = new PrintStream(new FileOutputStream(file))
      val sink = new Sink.print(stream)

      for (cmd <- prelude)
        sink.exec(cmd, null)

      val goal = !prop
      sink.exec(Assert(goal), null)
      sink.exec(CheckSat, null)

      prop
    }
  }
}

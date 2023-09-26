package cuvee.thesy

import cuvee.State
import cuvee.pure._
import cuvee.util.Tool
import cuvee.util.Name
import java.io.BufferedReader
import java.io.FileReader
import java.io.StringReader
import cuvee.smtlib.Solver

object TheSy {
  def main(args: Array[String]) {
    val lemmas = storedLemmas(
      "/home/ernst/Papers/adt-commute/benchmarks/ind/benchmarks-dt/isaplanner/goal82.smt2",
      "/home/ernst/Projects/cuvee/TheSy/experiments/cvc4_benchmarks/expl/isaplanner/goal82.smt2.log"
    )
    lemmas map println
  }

  def storedLemmas(smt2: String, th: String) = {
    val (cmds, st) = cuvee.smtlib.parse(smt2)
    val solver = Solver.z3(timeout = 100)
    for (cmd <- cmds)
      solver.exec(cmd, st)
    val in = new BufferedReader(new FileReader(th))
    readLemmas(in, st, solver)
  }

  def readLemmas(in: BufferedReader, st: State, solver: Solver) = {
    val PROVED = "proved: "
    val parser = new Parser(st)

    var line = in.readLine()
    var lemmas: List[Expr] = Nil

    while (line != null) {
      val pos = line.indexOf(PROVED)
      if (pos >= 0) {
        val rest = line.substring(pos + PROVED.length)
        val from = cuvee.sexpr.parse(new StringReader(rest))
        val eq = parser.rule(from)
        val expr = eq.toExpr
        
        lemmas = expr :: lemmas

        // if (solver.isTrue(expr)) {
        //   print("trivial: ")
        // } else
        //   solver.scoped {
        //     solver.assert(lemmas)
        //     if (solver.isTrue(expr))
        //       print("implied: ")
        //     else
        //       print("lemma:   ")

        //   }
        // println(eq)
      }

      line = in.readLine()
    }

    lemmas.reverse
  }

  def apply(file: String) {
    val (in, out, err, proc) = Tool.pipe("TheSy", file)

    var line = out.readLine()
    while (line != null) {
      val pos = line.indexOf("proved: ")
      if (pos >= 0) {
        val rest = ???
      }

      line = out.readLine()
    }
  }
}

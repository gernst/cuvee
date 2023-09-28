package cuvee.thesy

import java.io.File
import cuvee.pure._
import cuvee.smtlib._

object POPL2024 {
  val base_smt2 = "benchmarks-dt/"
  val base_th = "TheSy/experiments/cvc4_benchmarks/expl/"
  val categories = List("isaplanner")

  def main(args: Array[String]) {
    for (cat <- categories) {
      val dir = new File(base_smt2 + cat)
      for (goal <- dir.list().toList.sorted if goal.endsWith(".smt2")) {
        val smt2 = base_smt2 + cat + "/" + goal + ".log"

        try {
          print(cat + "/" + goal + " ")
          val (cmds, st) = cuvee.smtlib.parse(smt2)

          implicit val solver = Solver.z3(100)

          for (cmd <- cmds) cmd match {
            case SetLogic(_)      =>
            case _: Lemma         =>
            case Assert(Not(phi)) =>
            case _ =>
              solver.exec(cmd, null)
          }

          val ours = cmds collect { case Lemma(expr, _, _) =>
            expr
          }

          val th = base_th + cat + "/" + goal + ".log"
          //   println(th)
          val theirs = storedLemmas(th, st)

          ???
          // println(
          //   ours.length + " score = " + (theirs % ours) + " and " + theirs.length + " score = " + (ours % theirs)
          // )

          solver.ack(Exit)
          solver.destroy()
        } catch {
          case e: cuvee.smtlib.Error =>
            println(e.info)
          case e: Exception =>
            e.printStackTrace()
            println(e)
        }
      }
    }
  }
}

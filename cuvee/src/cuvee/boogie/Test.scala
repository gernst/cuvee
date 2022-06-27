package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.pure._
import cuvee.smtlib._

object _list extends Run(Test, "./list.bpl")
object _test extends Run(Test, "./test.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    val slv = z3(st)
    import cuvee.sexpr.Printer

    for(cmd <- cmds;
    lines <- cmd.lines) {
      println(lines)
    }
    // val prover = new Prove(slv)

    for (cmd ← cmds) {
      cmd match {
        case decl: Decl => slv.declare(decl)
        case Assert(Not(phi)) => {
          println("proving: " + phi)
          println("---------------  lines  ---------------")
          println(phi.lines(cuvee.boogie.Printer).mkString(""))
          println("--------------  is true  --------------")
          println(slv.isTrue(phi))
          println("=======================================")
        }
        case Lemma(expr, tactic) => {
          println("================  LEMMA  ================")
          println("show:" + expr)

          // val normalized = Disj.from(expr)
          val normalized = Disj.show(List(expr), Nil, Nil, Nil)
          if (tactic.isEmpty) {
            println("No tactic given.")
            // TODO: Consider what to do here. Call `prove` maybe?
          } else {
            println()
          }
        }
        case _ =>
      }
    }
  }

  def main(args: Array[String]): Unit = {
    for (arg <- args) {
      val (cmds, st) = cuvee.boogie.parse(arg)
      run(cmds, st)
    }
  }
}

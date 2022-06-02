package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.pure._
import cuvee.smtlib._

object _test extends Run(Test, "./test.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    val slv = z3(st)

    for (cmd ← cmds) {
      cmd match {
        case decl: Decl => slv.declare(decl)
        case Assert(Not(phi)) => {
          println("proving: " + phi)
          println("--------------  lines  --------------")
          println(phi.lines.mkString("\n"))
          println("-------------  is true  -------------")
          println(slv.isTrue(phi))

          // println("------------  disj show  ------------")
          // val phi_ = Simplifier.simplify(Disj.show(List(phi), Nil, Nil, Nil))
          // println(phi_)

          println("=====================================")
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

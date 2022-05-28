package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.pure._
import cuvee.smtlib._

object _test extends Run(Test, "test.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    cmds.reverse match {
      case Assert(Not(phi)) :: _ =>
        println("proving: " + phi)

      case _ =>

    }
  }

  def main(args: Array[String]): Unit = {
    for (arg <- args) {
      val (cmds, st) = parse(arg)
      run(cmds, st)
    }
  }
}

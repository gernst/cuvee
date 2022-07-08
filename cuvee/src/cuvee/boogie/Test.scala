package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.pure._
import cuvee.smtlib._
import cuvee.backend.Tactic

object _list extends Run(Test, "./list.bpl")
object _test extends Run(Test, "./test.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    val slv = z3(st)
    import cuvee.sexpr.Printer

    for (cmd ← cmds) {
      cmd match {
        case decl: Decl  => slv.declare(decl)
        case Assert(Not(phi)) => print(slv.isTrue(phi))
        case Assert(phi) => slv.assert(phi)
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

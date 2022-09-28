package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

import cuvee.State
import cuvee.backend._
import cuvee.pure._
import cuvee.smtlib._

object _list extends Run(Test, "./list.bpl")
object _test extends Run(Test, "./test.bpl")
object _prov extends Run(Test, "./prover.bpl")
object _smpl extends Run(Test, "./simple.bpl")

object Test extends Main {
  def run(cmds: List[Cmd], st: State) {
    import cuvee.sexpr.Printer

    val slv = z3(st)
    // val slv = new Sink.tee(z3(st), stdout)

    val prover = new Prove(slv)

    for (cmd ← cmds) {
      cmd match {
        case decl: Decl => slv.declare(decl)
        case Assert(Not(phi)) => {
          println("proving: " + phi)
          println("---------------  lines  ---------------")
          println(phi.lines(cuvee.boogie.Printer).mkString(""))
          println("--------------  is true  --------------")
          println(slv.isTrue(phi))
          println("--------------  to Disj  --------------")
          println(Disj.from(phi))
          println("---------------  prove  ---------------")
          val disj = Disj.from(phi);
          println(disj)
          val disj_ = prover.prove(disj)
          println(disj_)
          println(disj_.toExpr)
          // println("-------------  disprove  --------------")
          // println(prover.disprove(Conj.from(phi)).toExpr)
          println("=======================================")
          println()
        }
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

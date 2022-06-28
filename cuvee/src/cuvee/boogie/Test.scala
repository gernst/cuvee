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
          println("\n\n")
          println("================  LEMMA  ================")
          println("show:  " + expr)

          // val normalized = Disj.from(expr)
          val normalized = Disj.show(List(expr), Nil, Nil, Nil)

          if (tactic.isDefined) {
            rec(normalized, tactic.get, 1)
          } else {
            println("> open goal:  " + normalized)
            println("(no tactic given)")
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

  def rec(prop: Prop, tactic: Tactic, depth: Int = 0): Unit = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      if (depth <= 0) return "";
      indentStr + indent(depth - 1, indentStr)
    }

    println(indent(depth) + "---  PROOF OBLIGATION ---")
    println(indent(depth) + "prop:    " + prop)
    println(indent(depth) + "tactic:  " + tactic)
    val result = tactic.apply(prop)
    for((prop_, tactic_) <- result) {
      if (tactic_.isDefined) {
        rec(prop_, tactic_.get, depth + 1)
      } else {
        println(indent(depth) + "> open goal:  " + prop_)
        println(indent(depth) + "(no tactic given)")
      }
    }
  };
}

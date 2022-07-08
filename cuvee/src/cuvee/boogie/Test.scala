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
        case Assert(phi) => slv.assert(phi)
        case Lemma(expr, tactic) => {
          println()
          println("================  LEMMA  ================")
          println("show:  " + expr)

          // val normalized = Disj.from(expr)
          val normalized = Disj.show(List(expr), Nil, Nil, Nil)

          if (rec(normalized, tactic, 1)(st, slv))
            println("\u001b[92m✔\u001b[0m lemma proved successfully!")
          else
            println("\u001b[91m✘\u001b[0m could not prove the lemma!")
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

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      slv: solver
   ): Boolean = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      if (depth <= 0) return "";
      indentStr + indent(depth - 1, indentStr)
    }

    println(indent(depth) + "---  PROOF OBLIGATION ---")
    println(indent(depth) + "prop:    " + prop.toExpr)

    if (tactic.isDefined) {
      println(indent(depth) + "tactic:  " + tactic)
      val result = tactic.get.apply(state, prop)

      result.forall({ case (prop_, tactic_) => rec(prop_, tactic_, depth + 1) })
    } else {
      println(indent(depth) + "tactic:  none given, trying solver")

      val result = slv.isTrue(prop.toExpr)
      if (!result) {
        println(indent(depth + 1) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically")
        false
      } else {
        println(indent(depth + 1) + "\u001b[92m✔\u001b[0m goal confimed true by solver")
        true
      }
    }
  };
}

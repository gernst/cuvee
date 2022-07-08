package cuvee

import cuvee.backend.Tactic
import cuvee.pure._
import cuvee.smtlib._

class Cuvee {
  var state: Option[State] = None
  var cmds: List[Cmd] = Nil

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case path :: rest if state.isDefined =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        val (cmds_, state_) = cuvee.boogie.parse(path)
        state = Some(state_)
        cmds = cmds_

      case path :: rest if path.endsWith(".smt2") =>
        val (cmds_, state_) = cuvee.smtlib.parse(path)
        state = Some(state_)
        cmds = cmds_

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  def run() {
    assert(state.isDefined, "No file was parsed")

    val slv = z3(state.get)
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

          if (rec(normalized, tactic, 1)(state.get, slv))
            println("\u001b[92m✔\u001b[0m lemma proved successfully!")
          else
            println("\u001b[91m✘\u001b[0m could not prove the lemma!")
        }
        case _ =>
      }
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
        println(
          indent(
            depth + 1
          ) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
        )
        false
      } else {
        println(
          indent(
            depth + 1
          ) + "\u001b[92m✔\u001b[0m goal confimed true by solver"
        )
        true
      }
    }
  }
}

object Cuvee {
  def main(args: Array[String]) {
    val c = new Cuvee
    c.configure(args.toList)
    c.run()
  }
}

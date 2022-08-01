package cuvee

import cuvee.backend.Tactic
import cuvee.pure._
import cuvee.smtlib._
import cuvee.backend.Prove

class Cuvee {
  var state: Option[State] = None
  var cmds: List[Cmd] = Nil

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case "-debug:solver" :: rest =>
        cuvee.smtlib.solver.debug = true
        configure(rest)

      case path :: rest if state.isDefined =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        val (cmds_, state_) = cuvee.boogie.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        val (cmds_, state_) = cuvee.smtlib.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  def run() {
    assert(state.isDefined, "No file was parsed")

    val slv = z3(state.get)
    val prover = new Prove(slv)

    for (cmd ← cmds) {
      cmd match {
        case decl: Decl  => slv.declare(decl)
        case Assert(phi) => slv.assert(phi)
        case Lemma(expr, tactic) => {
          println()
          println("================  LEMMA  ================")
          println("show:  " + expr)

          val normalized = Disj.from(expr)

          if (rec(normalized, tactic, 1)(state.get, slv, prover))
            println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
          else
            println("\u001b[91m✘\u001b[0m Could not prove the lemma!")

          // In any case, assert the lemma, so that its statement is available in later proofs
          slv.assert(expr)
        }
        case _ =>
      }
    }
  }

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      slv: solver,
      prover: Prove
  ): Boolean = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      if (depth <= 0) return "";
      indentStr + indent(depth - 1, indentStr)
    }

    println(indent(depth) + "---  PROOF OBLIGATION ---")
    println(indent(depth) + "prop:     " + prop.toExpr)

    val simp = Simplifier.simplify(prop.toExpr)
    println(indent(depth) + "simp:     " + simp)

    (simp, tactic) match {
      case (True, _)  =>
        println(indent(depth + 1) + "\u001b[92m✔\u001b[0m Goal confimed true by simplifier")
        true
      case (False, _) =>
        println(indent(depth + 1) + "\u001b[91m✘\u001b[0m Goal was reduced to `false` by simplifier")
        false

      case (_, Some(tactic_)) =>
        println(indent(depth) + "tactic:   " + tactic)
        val result = tactic_.apply(state, prop)

        result.foldLeft(true) ({ case (acc, (prop_, tactic_)) =>
          rec(prop_, tactic_, depth + 1) && acc
        })

      case (_, _) =>
        println(indent(depth) + "tactic:   none given, trying simplifier and prover")

        var components: List[String] = Nil

        // Try a simplification first, without calling the prover
        components :+= "simplifier"
        val simp = (Simplifier.simplify(prop.toExpr) match {
          // Should this yield a boolean atom, no need to call the prover.
          case res@(True | False) =>
            res
          // Otherwise, call the prover …
          case simp_prop =>
            val res = prover.prove(prop).toExpr
            components :+= "prover"

            println(indent(depth + 1) + "new goal: " + res)
            // … and simplify the result
            Simplifier.simplify(res)
        })

        println(indent(depth + 1) + "simp:     " + simp)

        simp match {
          case True =>
            println(indent(depth + 1) + f"\u001b[92m✔\u001b[0m Goal transformed to `true` by ${components.mkString(", ")}")
            true

          case False => 
            println(indent(depth + 1) + f"\u001b[91m✘\u001b[0m Goal transformed to `false` by ${components.mkString(", ")}")
            false

          case goal =>
            println(indent(depth + 2) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically")
            false
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

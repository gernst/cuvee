package cuvee.util

import cuvee.backend._
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.pure._
import cuvee.State
import cuvee.smtlib.Lemma

object Proving {
  var debug = false

  def show(prop: Prop, tactic: Option[Tactic])(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      printer: Printer,
      rules: Map[Fun, List[Rule]] = Map()
  ): Prop = {
    val res = rec(prop, tactic, 1)(state, solver, prover, rules)
    res match {
      case Atom(True) | Disj(_, _, List(Atom(True))) =>
        // hack around incomplete simplification
        if (debug)
          println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
      case Atom(False) =>
        if (debug)
          println(
            "\u001b[91m✘\u001b[0m The lemma is false and cannot be proven!"
          )
      case remaining if printer == cuvee.boogie.printer =>
        val lines = remaining match {
          case Atom(expr) =>
            expr.lines

          case Conj(xs, neg) =>
            var result: List[String] = Nil

            val bound =
              for (x <- xs)
                yield "  " + x.name.toLabel + ": " + x.typ

            val indent = if (bound.isEmpty) "" else "  "

            val concls =
              for (
                phi <- neg;
                line <- phi.lines
              )
                yield indent + line

            if (bound.nonEmpty)
              result ++= List("exists") ++ bound

            if (concls.size == 1)
              result ++= concls

            result

          case Disj(xs, neg, pos) =>
            var result: List[String] = Nil

            val bound =
              for (x <- xs)
                yield "  " + x.name.toLabel + ": " + x.typ

            val assms =
              for (
                phi <- neg;
                line <- phi.lines
              )
                yield "  " + line

            val concls =
              for (
                phi <- pos;
                line <- phi.lines
              )
                yield "  " + line

            if (bound.nonEmpty)
              result ++= List("forall") ++ bound

            if (assms.nonEmpty)
              result ++= List("assume") ++ assms

            if (concls.isEmpty)
              result ++= List("show contradiction")

            if (concls.size == 1)
              result ++= List("show") ++ concls

            if (concls.size > 1)
              result ++= List("show one of") ++ concls

            result
        }

        println("lemma")
        for (line <- lines)
          println("  " + line)
        println("  sorry")
        println()

      case remaining =>
        if (debug)
          println(
            "\u001b[91m⚠\u001b[0m Some subgoals could not be proven! Remaining combined goal: " + remaining
          )
        val cmd = Lemma(remaining.toExpr, None);
        for (line <- cmd.lines)
          println(line)
    }

    res
  }

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      rules: Map[Fun, List[Rule]]
  ): Prop = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      indentStr * depth
    }

    if (debug) {
      println(indent(depth) + "---  PROOF OBLIGATION ---")
      println(indent(depth) + "prop:     " + prop.toExpr)
    }

    // Call the prover, except if instructed by the NoAuto tactic *not* to do so.
    // Sets `tactic_` to an `Option[Tactic]` of the tactic that should be applied to the remaining goal (if any)
    val (tactic_, prop_) = tactic match {
      case Some(NoAuto(tactic_)) =>
        // Skip the prover call and execute the inner tactic directly
        (Some(tactic_), prop)

      // Also, skip the prover call, if the next tactic on the "prover blacklist", that follows.
      case Some(Induction(_, _)) | Some(Show(_, _, _)) =>
        (tactic, prop)

      case _ =>
        // Call prover
        val res = prover.prove(prop)
        if (debug)
          println(indent(depth) + "new goal: " + res.toExpr)

        // Set tactic_ to whatever tactic was beforehand
        (tactic, res)
    }

    // Apply the tactic `tactic_`
    val prop__ = tactic_ match {
      case Some(tactic_) =>
        if (debug)
          println(indent(depth) + "tactic:   " + tactic)

        // Apply the tactic and get the remaining subgoals that we need to prove
        val goals = tactic_.apply(state, prop)

        // TODO: What do we return, if not all of the subgoals can be proven?
        //       Do we return /\ {unprovable subgoals} ?
        (goals map ({ case (prop_, tactic_) =>
          rec(prop_, tactic_, depth + 1)
        }) filter (_ != Atom(True))) match {
          case Nil             => Atom(True)
          case remaining_goals => Conj.from(remaining_goals map (_.toExpr))
        }
      case None => prop_
    }

    // Call the simplifier
    val simp = Simplify.simplify(prop__, rules)
    if (debug)
      println(indent(depth) + "simp:     " + simp.toExpr)

      simp match {
        case Atom(True) =>
          println(
            indent(depth) + f"\u001b[92m✔\u001b[0m Goal found to be `true`"
          )

        case Atom(False) =>
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Goal found to be `false`"
          )

        case goal =>
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
          )
      }

    // Return whatever remained
    simp
  }
}

package cuvee.util

import cuvee.backend._
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.pure._
// import cuvee.smtlib._
import cuvee.boogie.printer
import cuvee.State
import cuvee.smtlib.Lemma

object Proving {
  var debug = false

  def show(prop: Prop, tactic: Option[Tactic])(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      rules: Map[Fun, List[Rule]] = Map()
  ): Prop = {
    val res = rec(prop, tactic, 1)(state, solver, prover, rules)
    res match {
      case Atom(True) =>
        if (debug)
          println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
      case Atom(False) =>
        if (debug)
          println(
            "\u001b[91m✘\u001b[0m The lemma is false and cannot be proven!"
          )
      case remaining =>
        if (debug)
          println(
            "\u001b[91m⚠\u001b[0m Some subgoals could not be proven! Remaining combined goal: " + remaining.toExpr
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
          case remaining_goals => Conj.from(And(remaining_goals map (_.toExpr)))
        }
      case None => prop_
    }

    // Call the simplifier
    val simp = Simplify.simplify(prop__, rules)
    if (debug)
      println(indent(depth) + "simp:     " + simp.toExpr)

    simp match {
      case Atom(True) =>
        if (debug)
          println(
            indent(depth) + f"\u001b[92m✔\u001b[0m Goal found to be `true`"
          )

      case Atom(False) =>
        if (debug)
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Goal found to be `false`"
          )

      case goal =>
        if (debug)
          println(
            indent(
              depth
            ) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
          )
    }

    // Return whatever remained
    simp
  }
}

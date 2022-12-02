package cuvee.util

import cuvee.backend._
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.pure._
import cuvee.State
import cuvee.smtlib._

object Proving {
  var debug = false

  var suggestTactics: Boolean = false
  var applyTactics: Boolean = false

  def show(prop: Prop, tactic: Option[Tactic])(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      printer: Printer,
      rules: Map[Fun, List[Rule]] = Map()
  ): Prop = {
    val res = rec(prop, tactic, 1)(state, solver, prover, rules)
    res match {
      case Atom.t | Disj(_, _, List(Atom.t)) =>
        // hack around incomplete simplification
        if (debug)
          println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
      case Atom.f =>
        if (debug)
          println(
            "\u001b[91m✘\u001b[0m The lemma is false and cannot be proven!"
          )
      case remaining if printer == cuvee.boogie.printer =>
        val lines = printer.lines(remaining)

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

  def rec(prop_ : Prop, tactic_ : Option[Tactic], depth: Int = 0)(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      rules: Map[Fun, List[Rule]]
  ): Prop = {
    var prop: Prop = prop_
    var tactic: Option[Tactic] = tactic_

    if (debug) {
      println(indent(depth) + "---  PROOF OBLIGATION ---")
      println(indent(depth) + "prop:     " + prop.toExpr)
      println(indent(depth) + "comp:     " + Rating.complexity(prop))
    }

    // Call the prover, except if instructed by the NoAuto tactic *not* to do so.
    // Sets `tactic` to an `Option[Tactic]` of the tactic that should be applied to the remaining goal (if any)
    tactic match {
      // Skip the prover call and execute the inner tactic directly
      case Some(NoAuto(inner)) => tactic = Some(inner)

      // Also, skip the prover call, if the next tactic on the "prover blacklist", that follows.
      case Some(Induction(_, _)) | Some(Show(_, _, _)) => ()

      // Otherwise, rewrite prop by applying the prover and simplifying
      case _ => prop = proveAndSimplify(prop, prover, debug, depth)
    }

    // If there is no tactic and suggestion / automatic application is enabled,
    // try to find an applicable tactic.
    if (tactic.isEmpty && (suggestTactics || applyTactics)) {
      // Get suggestions
      val suggestions = Suggest.suggest(state, prop)

      // If there is no tactic given, find one that could be used automatically
      if (applyTactics) {
        val candidates =
          for (tac <- suggestions ; prog <- tac.makesProgress(state, prop))
            yield (tac, prog)

        tactic = candidates.maxByOption(_._2).map(_._1)
      }

      // Suggest tactics. If a tactic for automatic application was found, make this the default
      if (suggestTactics) {
        if (suggestions.nonEmpty) {
          println(indent(depth) + "goal:     " + prop)

          tactic = CLI.askChoices(
            "Do you want to apply one of the following tactics?",
            suggestions,
            default = Some(suggestions.indexOf(tactic.getOrElse(None))),
            printfn = (str => print(indent(depth + 1) + str))
          )
        }
      }
    }

    // Apply the tactic `tactic_`
    if (tactic.isDefined)
    {
      val tactic_ = tactic.get

      if (debug)
        println(indent(depth) + "tactic:   " + tactic_)

      // Apply the tactic and get the remaining subgoals that we need to prove
      val goals = tactic_.apply(state, prop)

      prop = (goals map ({ case (prop, tactic) =>
        rec(prop, tactic, depth + 1)
      }) filter (_ != Atom(True))) match {
        case Nil             => Atom(True)
        case remaining_goals => Conj.from(remaining_goals map (_.toExpr))
      }
    }

    // Simplify the result
    val simp = Simplify.simplify(prop, rules)
    if (debug)
      println(indent(depth) + "simp:     " + simp)

    simp match {
      case Atom.t =>
        if (debug)
          println(
            indent(depth) + f"\u001b[92m✔\u001b[0m Goal found to be `true`"
          )

      case Atom.f =>
        if (!debug)
          println(indent(depth) + "simp:     " + simp)

        if (debug)
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Goal found to be `false`"
          )

      case goal =>
        if (!debug)
          println(indent(depth) + "simp:     " + simp)

        if (debug)
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
          )
    }

    // Return whatever remained
    simp
  }

  def proveAndSimplify(
      prop: Prop,
      prover: Prove,
      debug: Boolean = false,
      depth: Int = 0
  )(implicit rules: Map[Fun, List[Rule]] = Map()): Prop = {
    // Call prover
    val res = prover.prove(prop)
    if (debug)
      println(indent(depth) + "new goal: " + res.toExpr)

    // Simplify the result
    val simp = Simplify.simplify(res, rules)
    if (debug)
      println(indent(depth) + "simp:     " + simp.toExpr)

    simp
  }

  private[this] def indent(depth: Int, indentStr: String = "  "): String = indentStr * depth
}

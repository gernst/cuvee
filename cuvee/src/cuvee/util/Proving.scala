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

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      solver: Solver,
      prover: Prove,
      rules: Map[Fun, List[Rule]]
  ): Prop = {
    if (debug) {
      println(indent(depth) + "---  PROOF OBLIGATION ---")
      println(indent(depth) + "prop:     " + prop.toExpr)
      println(indent(depth) + "comp:     " + Rating.complexity(prop))
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
        val res = proveAndSimplify(prop, prover, debug, depth)

        // Set tactic_ to whatever tactic was beforehand
        (tactic, res)
    }

    // If there is no tactic given, suggest one
    val tactic__ = tactic_ match {
      case None if applyTactics =>
        // Get suggestions
        val suggestions = Suggest.suggest(state, prop_)

        val foo =
          for (tac <- suggestions ; prog <- tac.makesProgress(state, prop_))
            yield (tac, prog)

        None

      case None if suggestTactics =>
        // Get suggestions
        val suggestions = Suggest.suggest(state, prop_)

        if (suggestions.nonEmpty) {
          println(indent(depth) + "goal:     " + prop_)

          val choice = CLI.askChoices(
            "Do you want to apply one of the following tactics?",
            suggestions,
            default = Some(-1),
            printfn = (str => print(indent(depth + 1) + str))
          )
          choice
        } else {
          None
        }

      case t => t
    }

    // Apply the tactic `tactic_`
    val prop__ = tactic__ match {
      case Some(tactic_) =>
        if (debug)
          println(indent(depth) + "tactic:   " + tactic_)

        // Apply the tactic and get the remaining subgoals that we need to prove
        val goals = tactic_.apply(state, prop)

        (goals map ({ case (prop_, tactic_) =>
          rec(prop_, tactic_, depth + 1)
        }) filter (_ != Atom(True))) match {
          case Nil             => Atom(True)
          case remaining_goals => Conj.from(remaining_goals map (_.toExpr))
        }
      case None => prop_
    }

    // Simplify the result
    val simp = Simplify.simplify(prop__, rules)
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

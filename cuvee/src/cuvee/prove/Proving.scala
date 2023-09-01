package cuvee.prove

import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.pure._
import cuvee.State
import cuvee.smtlib._
import cuvee.util.Printer
import cuvee.util.CLI

object Proving {
  var debug = false

  var suggestTactics: Boolean = false
  var applyTactics: Boolean = false

  def show(prop: Prop, tactic: Option[Tactic])(implicit
      state: State,
      solver: Solver,
      prover: Prover,
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
        println()

      case remaining =>
        if (debug)
          println(
            "\u001b[91m⚠\u001b[0m Some subgoals could not be proven! Remaining combined goal: " + remaining
          )
        val cmd = Lemma(remaining.toExpr, None, false);
        for (line <- cmd.lines)
          println(line)
    }

    res
  }

  def rec(prop_ : Prop, tactic_ : Option[Tactic], depth: Int = 0)(implicit
      state: State,
      solver: Solver,
      prover: Prover,
      rules: Map[Fun, List[Rule]]
  ): Prop = {
    var prop: Prop = prop_
    var tactic: Option[Tactic] = tactic_

    if (debug) {
      println(indent(depth) + "---  PROOF OBLIGATION ---")
      println(indent(depth) + "prop:     " + prop.toExpr)
      println(indent(depth) + "size:     " + Rating.size(prop))
    }

    // Call the prover, except if instructed by the NoAuto tactic *not* to do so.
    // Sets `tactic` to an `Option[Tactic]` of the tactic that should be applied to the remaining goal (if any)
    tactic match {
      // Skip the prover call and execute the inner tactic directly
      case Some(NoAuto(inner)) => tactic = Some(inner)

      // Otherwise, rewrite prop by applying the prover and simplifying
      case _ => prop = proveAndSimplify(prop, prover, state, debug, depth)
    }

    // If there is no tactic and suggestion / automatic application is enabled,
    // try to find an applicable tactic.
    if (tactic.isEmpty && (suggestTactics || applyTactics)) {
      // Get suggestions
      val suggestions = suggestTactics match {
        case true  => Suggest.suggest(state, prop)
        case false => Suggest.suggestAuto(state, prop)
      }

      // If there is no tactic given, find one that could be used automatically
      if (applyTactics) {
        val candidates =
          for (tac <- suggestions; prog <- tac.makesProgress(state, prop))
            yield (tac, prog)

        tactic = candidates.maxByOption(_._2).map(_._1)
      }

      // Suggest tactics. If a tactic for automatic application was found, make this the default
      if (suggestTactics) {
        if (suggestions.nonEmpty) {
          val lines = cuvee.boogie.printer.lines(prop)

          println(indent(depth + 1) + "current goal:")
          for (line <- lines)
            println(indent(depth + 1) + "  " + line)
          println()

          tactic = CLI.askChoices(
            "Do you want to apply one of the following tactics? [  ] = default",
            suggestions,
            default = Some(suggestions.indexOf(tactic.getOrElse(None))),
            printfn = (str => print(indent(depth + 1) + str))
          )
        }
      }
    }

    // Apply the tactic in `tactic`
    if (tactic.isDefined) {
      val tactic_ = tactic.get

      if (debug)
        println(indent(depth) + "tactic:   " + tactic_)

      // Apply the tactic and get the remaining subgoals that we need to prove
      val goals = tactic_.apply(state, prop)

      prop = (goals map ({ case (prop, tactic) =>
        rec(prop, tactic, depth + 1)
      }) filter (_ != Atom(True))) match {
        case Nil             => Atom(True)
        case remaining_goals => ??? // Conj.from(remaining_goals map (_.toExpr))
      }
    }

    // Simplify the result
    val simp = Simplify.simplify(prop, rules, state.constrs)
    if (debug)
      println(indent(depth) + "simp:     " + simp)

    simp match {
      case Atom.t =>
        if (debug)
          println(
            indent(depth) + f"\u001b[92m✔\u001b[0m Goal found to be `true`"
          )

      case Atom.f =>
        if (debug)
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Goal found to be `false`"
          )

      case goal =>
        if (debug)
          println(
            indent(depth) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} by reduction"
          )
    }

    // Return whatever remained
    simp
  }

  def proveAndSimplify(
      prop: Prop,
      prover: Prover,
      state: State,
      debug: Boolean = false,
      depth: Int = 0
  )(implicit rules: Map[Fun, List[Rule]] = Map()): Prop = {
    // Call prover
    val res = prover.reduce(prop, state)
    if (debug)
      println(indent(depth) + "new goal: " + res.toExpr)

    // Simplify the result
    val simp = Simplify.simplify(res, rules, state.constrs)
    if (debug)
      println(indent(depth) + "simp:     " + simp)

    simp
  }

  private[this] def indent(depth: Int, indentStr: String = "  "): String =
    indentStr * depth
}

package cuvee.prove

import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

import cuvee.pure._
import cuvee.sub
import cuvee.smtlib.Assert

class Prove(
    prover: Prover,
    simplify: Boolean,
    rewrite: Boolean,
    proveNegatedAsserts: Boolean = true
) extends Stage {
  def exec(prefix: List[Cmd], cmds: List[Cmd], state: State) = {
    val rws = if (rewrite) {
      val rules = Rewrite.from(prefix ++ cmds, state) // add some new rewrite rules
      rules.groupBy(_.fun) // update rule index
    } else {
      Map[Fun, List[Rule]]()
    }

    cmds flatMap {
      case cmd @ Lemma(expr, tactic, assert) =>
        val goal = Prop.from(expr)
        for (goal_ <- reduce(goal, tactic, rws, state) if !goal_.isTrue)
          yield Lemma(goal_.toExpr, None, assert)

      case cmd @ Assert(Not(expr)) if proveNegatedAsserts =>
        val goal = Prop.from(expr)
        for (goal_ <- reduce(goal, None, rws, state))
          yield Assert(Simplify.not(goal_.toExpr))

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  def auto(goal: Prop, rws: Map[Fun, List[Rule]], state: State) = if (simplify) {
    val goal_ = Simplify.simplify(goal, rws, state.constrs)
    prover.reduce(goal_, state)
  } else {
    prover.reduce(goal, state)
  }

  def reduce(
      goal: Prop,
      tactic: Option[Tactic],
      rws: Map[Fun, List[Rule]],
      state: State
  ): List[Prop] = tactic match {
    case None =>
      List(auto(goal, rws, state))

    case Some(tactic) =>
      reduce(goal, tactic, rws, state)
  }

  def reduce(goal: Prop, tactic: Tactic, rws: Map[Fun, List[Rule]], state: State): List[Prop] =
    tactic match {
      case NoAuto(tactic) =>
        noauto(goal, tactic, rws, state)

      case _: Induction | _: Show =>
        noauto(goal, tactic, rws, state)

      case Auto =>
        List(auto(goal, rws, state))

      case Sorry =>
        List(goal)

      case _ =>
        noauto(auto(goal, rws, state), tactic, rws, state)
    }

  def noauto(goal: Prop, tactic: Tactic, rws: Map[Fun, List[Rule]], state: State): List[Prop] =
    tactic match {
      case NoAuto(tactic) =>
        noauto(goal, tactic, rws, state) // yeah, you can write noauto twice

      case Auto =>
        ??? // should never happen

      case _ =>
        for (
          (subgoal, subtactic) <- tactic.apply(state, goal);
          goal_ <- reduce(subgoal, subtactic, rws, state)
        )
          yield goal_
    }
}

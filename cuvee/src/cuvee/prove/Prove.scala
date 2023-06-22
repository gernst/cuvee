package cuvee.prove

import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

import cuvee.pure._
import cuvee.sub

class Prove(state: State = State.default, prover: Prover) extends Stage {
  def copy() = new Prove(state.copy(), prover)

  def apply(prefix: List[Cmd], cmds: List[Cmd]): List[Cmd] = cmds map {
    case Lemma(expr, tactic, assert) =>
      val goal = Disj.from(expr)
      val goal_ = reduce(goal, tactic)
      val expr_ = goal_.toExpr
      Lemma(expr_, None, assert)

    case cmd =>
      cmd
  }

  def auto(goal: Prop) = {
    prover.reduce(goal)
  }

  def reduce(goal: Prop, tactic: Option[Tactic]): Prop = tactic match {
    case None =>
      auto(goal)

    case Some(tactic) =>
      reduce(goal, tactic)
  }

  def reduce(goal: Prop, tactic: Tactic): Prop = tactic match {
    case NoAuto(tactic) =>
      noauto(goal, tactic)

    case Auto =>
      auto(goal)

    case _ =>
      noauto(auto(goal), tactic)
  }

  def noauto(goal: Prop, tactic: Tactic): Prop = tactic match {
    case NoAuto(tactic) =>
      noauto(goal, tactic) // yeah, you can write noauto twice

    case Auto =>
      ??? // should never happen

    case _ =>
      val goals_ =
        for ((subgoal, subtactic) <- tactic.apply(state, goal))
          yield reduce(subgoal, subtactic)

      Conj.show(goals_, Nil, Nil)
  }
}

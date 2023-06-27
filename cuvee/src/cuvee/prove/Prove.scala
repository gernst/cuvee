package cuvee.prove

import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

import cuvee.pure._
import cuvee.sub

class Prove(prover: Prover) extends Stage {
  def exec(prefix: List[Cmd], cmds: List[Cmd], state: State) = {
    cmds flatMap {
      case Lemma(expr, tactic, assert) =>
        val goal = Disj.from(expr)
        for (goal_ <- reduce(goal, tactic, state) if goal_ != Atom.t)
          yield Lemma(goal_.toExpr, None, assert)

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  def auto(goal: Prop) = {
    prover.reduce(goal, null)
  }

  def reduce(goal: Prop, tactic: Option[Tactic], state: State): List[Prop] = tactic match {
    case None =>
      List(auto(goal))

    case Some(tactic) =>
      reduce(goal, tactic, state)
  }

  def reduce(goal: Prop, tactic: Tactic, state: State): List[Prop] = tactic match {
    case NoAuto(tactic) =>
      noauto(goal, tactic, state)

    case _: Induction | _: Show =>
      noauto(goal, tactic, state)

    case Auto =>
      List(auto(goal))

    case _ =>
      noauto(auto(goal), tactic, state)
  }

  def noauto(goal: Prop, tactic: Tactic, state: State): List[Prop] = tactic match {
    case NoAuto(tactic) =>
      noauto(goal, tactic, state) // yeah, you can write noauto twice

    case Auto =>
      ??? // should never happen

    case _ =>
      for (
        (subgoal, subtactic) <- tactic.apply(state, goal);
        goal_ <- reduce(subgoal, subtactic, state)
      )
        yield goal_
  }
}

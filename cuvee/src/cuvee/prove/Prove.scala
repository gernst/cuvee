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
  var rules: List[Rule] = Nil
  var rws: Map[Fun, List[Rule]] = Map()

  def exec(prefix: List[Cmd], cmds: List[Cmd], state: State) = {
    if (rewrite) {
      rules ++= Rewrite.from(cmds, state) // add some new rewrite rules
      rws = rules.groupBy(_.fun) // update rule index
    }

    cmds flatMap {
      case cmd @ Lemma(expr, tactic, assert) =>
        val goal = Prop.from(expr)
        for (goal_ <- reduce(goal, tactic, state) if !goal_.isTrue)
          yield Lemma(goal_.toExpr, None, assert)

      case cmd @ Assert(Not(expr)) if proveNegatedAsserts =>
        val goal = Prop.from(expr)
        for (goal_ <- reduce(goal, None, state))
          yield Assert(Not(goal_.toExpr))

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  def auto(goal: Prop, state: State) = if (simplify) {
    val goal_ = Simplify.simplify(goal, rws, state.constrs)
    prover.reduce(goal_, state)
  } else {
    prover.reduce(goal, state)
  }

  def reduce(goal: Prop, tactic: Option[Tactic], state: State): List[Prop] = tactic match {
    case None =>
      List(auto(goal, state))

    case Some(tactic) =>
      reduce(goal, tactic, state)
  }

  def reduce(goal: Prop, tactic: Tactic, state: State): List[Prop] = tactic match {
    case NoAuto(tactic) =>
      noauto(goal, tactic, state)

    case _: Induction | _: Show =>
      noauto(goal, tactic, state)

    case Auto =>
      List(auto(goal, state))

    case Sorry =>
      List(goal)

    case _ =>
      noauto(auto(goal, state), tactic, state)
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

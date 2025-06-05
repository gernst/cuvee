package cuvee.prove

import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

import cuvee.pure._
import cuvee.sub
import cuvee.smtlib.Assert
import cuvee.smtlib.Solver
import cuvee.smtlib.Free
import cuvee.smtlib.DeclareVar
import cuvee.smtlib.DeclareSort
import cuvee.smtlib.Goal

class Prove(
    prover: Prover,
    simplify: Boolean,
    rewrite: Boolean,
    proveNegatedAsserts: Boolean,
    crosscheckProver: Boolean
) extends Stage {
  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) = {
    val results = exec(prefix, cmds, state)
    prover.exec(last, state)
    results
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], state: State) = {
    val rws = if (rewrite) {
      val rules = Rewrite.from(prefix ++ cmds, state) // add some new rewrite rules
      rules.groupBy(_.fun) // update rule index
    } else {
      Map[Fun, List[Rule]]()
    }

    cmds flatMap {
      case cmd @ Lemma(expr, tactic, Some(Free), label) =>
        prover.exec(cmd, state)
        List(cmd)

      case cmd @ Lemma(expr, tactic, Some(Goal), label) =>
        val goal = expr
        for (goal_ <- reduce(goal, tactic, rws, state) if !(goal_ == True))
          yield {
            val expr_ = goal_
            crosscheck(expr, goal, goal_, expr_, prefix ++ cmds, state)
            Lemma(expr_, None, Some(Goal), label)
          }

      case cmd @ Lemma(expr, tactic, None, label) =>
        val goal = expr
        for (goal_ <- reduce(goal, tactic, rws, state))
          yield {
            val expr_ = goal_
            crosscheck(expr, goal, goal_, expr_, prefix ++ cmds, state)
            val mode_ = if (expr_ == True) Some(Free) else None
            Lemma(expr, None, mode_, label)
          }

      case cmd @ Assert(Not(App(Inst(fun, _), _)))
          if proveNegatedAsserts && (rws contains fun) && rws(fun).nonEmpty =>
        // println(rws(fun))
        prover.exec(cmd, state)
        List(cmd)

      case cmd @ Assert(Not(expr)) if proveNegatedAsserts =>
        val goal = expr
        // println("proving " + goal)
        // println(rws)
        for (goal_ <- reduce(goal, None, rws, state))
          yield {
            val expr_ = goal_
            crosscheck(expr, goal, goal_, expr_, prefix ++ cmds, state)
            Assert(Simplify.not(expr_))
          }

      case cmd: DeclareVar =>
        List(cmd)

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  def crosscheck(
      expr: Expr,
      goal: Expr,
      goal_ : Expr,
      expr_ : Expr,
      ctx: List[Cmd],
      state: State
  ) = {
    if (crosscheckProver) {
      val solver = Solver.cvc5(timeout = 10000)
      try {
        ctx foreach {
          case _: Lemma =>
          case cmd =>
            solver.exec(cmd, state)
        }
      } catch {
        case cuvee.smtlib.Error(info) =>
          println(info)
        // ???
      }

      if (!solver.isTrue(expr === goal)) {
        println(expr)
        println(goal)
        assert(false, "conversion to prop did not produce original formula!")
      }

      if (!solver.isTrue(expr_ === goal_)) {
        // println(expr)
        assert(false, "conversion to prop did not produce reduced formula!")
      }

      if (!solver.isTrue(expr === expr_)) {
        println(expr + " != " + expr_)
        assert(false, "reduce did not produce formulas recognized equivalent!")
      }
    }

  }

  def auto(goal: Expr, rws: Map[Fun, List[Rule]], state: State) = if (simplify) {
    val goal_ = Simplify.simplify(goal, rws, state.constrs)
    prover.reduce(goal_, state)
  } else {
    val goal_ = prover.reduce(goal, state)
    goal_
  }

  def reduce(
      goal: Expr,
      tactic: Option[Proof],
      rws: Map[Fun, List[Rule]],
      state: State
  ): List[Expr] = tactic match {
    case None =>
      List(auto(goal, rws, state))

    case Some(tactic) =>
      reduce(goal, tactic, rws, state)
  }

  def reduce(goal: Expr, proof: Proof, rws: Map[Fun, List[Rule]], state: State): List[Expr] =
    proof.tactic match {
      case NoAuto =>
        noauto(goal, ???, Nil, rws, state)

      case _: Induction | _: Show =>
        val tactic = proof.tactic
        noauto(goal, proof, Nil, rws, state)

      case Auto =>
        List(auto(goal, rws, state))

      case Sorry =>
        List(goal)

      case _ =>
        noauto(auto(goal, rws, state), proof, Nil, rws, state)
    }

  def noauto(goal: Expr, tactic: Proof , subproof: List[(Sel, Proof)], rws: Map[Fun, List[Rule]], state: State): List[Expr] =
    tactic.tactic match {
      case NoAuto =>
        //TODO mathcing
        noauto(goal, Proof(Auto, Nil), Nil, rws, state) // yeah, you can write noauto twice

      case Auto =>
        ??? // should never happen

      case _ =>
        for (
          (sel, subgoal) <- ProofUtils.apply(goal, tactic.tactic, state, Nil);
          //TODO find proof with matching sel in subproofs 
          goal_ <- reduce(subgoal, Proof(Auto, Nil), rws, state)
        ) yield {
          goal_
        }
    }
}

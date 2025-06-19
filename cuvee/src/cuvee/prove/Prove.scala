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
        for (expr_ <- reduce(expr, tactic, rws, state, cmds) if !(expr_ == True))
          yield {
            Lemma(expr_, None, Some(Goal), label)
          }

      case cmd @ Lemma(expr, tactic, None, label) =>
        val exprs_ = reduce(expr, tactic, rws, state, cmds)
        exprs_ match {
          case Nil =>
            // was proved! take original as free lemma
            val cmd_ = Lemma(expr, None, Some(Free), label)
            prover.exec(cmd_, state)
            List(cmd_)

          case _ =>
            for (expr_ <- exprs_)
              yield Lemma(expr, None, None, label)
        }

      case cmd @ Assert(Not(App(Inst(fun, _), _)))
          if proveNegatedAsserts && (rws contains fun) && rws(fun).nonEmpty =>
        prover.exec(cmd, state)
        List(cmd)

      case cmd @ Assert(Not(expr)) if proveNegatedAsserts =>
        for (expr_ <- reduce(expr, None, rws, state, cmds))
          yield {
            Assert(Simplify.not(expr_))
          }

      case cmd: DeclareVar =>
        List(cmd)

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  def reduce(
      goal: Expr,
      proof: Option[Proof],
      rws: Map[Fun, List[Rule]],
      state: State,
      cmds: List[Cmd]
  ): List[Expr] = proof match {
    case None         => reduce(goal, Proof(Auto, Nil), rws, state, cmds)
    case Some(proof_) => reduce(goal, proof_, rws, state, cmds)
  }

  def reduce(
      goal: Expr,
      proof: Proof,
      rws: Map[Fun, List[Rule]],
      state: State,
      cmds: List[Cmd]
  ): List[Expr] = {
    // print(cuvee.boogie.Printer.proof(proof))
    val attempt = ProofUtils.apply(goal, proof, state, prover, rws)
    val tree = TreeUtils.insertAttempt(Nil, Step(goal), attempt)
    // println(tree.toString(0))
    tree.leaves
  }

  def noauto(
      goal: Expr,
      proof: Proof,
      rws: Map[Fun, List[Rule]],
      state: State,
      cmds: List[Cmd]
  ): List[Expr] =
    proof match {
      case Proof(NoAuto, Nil) =>
        reduce(goal, Proof(BreakPoint, Nil), rws, state, cmds)

      case Proof(NoAuto, cont) =>
        for (
          (sel, subproof) <- cont;
          goal_ <- reduce(goal, subproof, rws, state, cmds)
        ) // yeah, you can write noauto twice
          yield goal_

      case Proof(Auto, _) =>
        ??? // should never happen

      case Proof(tactic, subproofs) =>
        for (
          (sel, subgoal) <- ProofUtils.apply(goal, tactic, state, prover, rws);
          goal_ <- reduce(subgoal, Proof(???, ???), rws, state, cmds)
        ) yield {
          goal_
        }
    }
}

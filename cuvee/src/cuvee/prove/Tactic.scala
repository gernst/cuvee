package cuvee.prove

import cuvee.pure._
import cuvee.sub
import cuvee.State
import cuvee.util.Name
import cuvee.smtlib._
import cuvee.pipe.Stage
import scala.collection.DoubleStepper
import scala.io.StdIn

trait Sel{
  def matches(sel: Sel): Boolean
}

case class ConstrSel(constructor: Fun, variables: List[Var]) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case ConstrSel(cons, vars) => 
      cons == constructor
    case _ => false
  }
  
  override def toString = variables match{
    case Nil => "case " + constructor.name + " => "
    case _ => "case " + constructor.name + variables.mkString("(", ",", ")") + " => " 
  }
}

case object ProofSel extends Sel{
  def matches(sel: Sel): Boolean = sel == ProofSel
  override def toString = "proof "
}

case object ThenSel extends Sel{
    def matches(sel: Sel): Boolean = sel == ThenSel
    override def toString = "then "
}

case class IndexSel(index: BigInt) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case IndexSel(index_) => index_ == index
    case _ => false 
  }

  override def toString = "case " + index + " => "
}

trait Tactic {}
case class Induction(x: Var) extends Tactic
case class Show(expression: Expr) extends Tactic
case class Unfold(target: (Name, Int), places: Option[List[BigInt]]) extends Tactic
case object NoAuto extends Tactic
case object Auto extends Tactic
case object BreakPoint extends Tactic
case object Sorry extends Tactic
case object Split extends Tactic

case class Proof(tactic: Tactic, subproofs: List[(Sel, Proof)])

object ProofUtils{
  def match_subproof_to_subgoals(pat: Sel, subproof: Proof, subgoals: List[(Sel, Expr)]): ((Sel, Expr, Proof), List[(Sel, Expr)]) = 
    (pat, subgoals) match {
      case (_, Nil) =>
        ???

      case (ConstrSel(sel, vars), (ConstrSel(sel_, vars_), subgoal) :: restgoals) if sel == sel_ =>
        val re = Expr.subst(vars_, vars)
        val Clause(xs, ant, suc) = subgoal
        val subgoal_ = Clause(xs rename re, ant rename re, suc rename re)
        ((pat, subgoal_, subproof), restgoals)

      case (ThenSel, (ThenSel, subgoal) :: restgoals) =>
        ((pat, subgoal, subproof), restgoals)

      case (ProofSel, (ProofSel, subgoal) :: restgoals) => 
        ((pat, subgoal, subproof), restgoals)

      case (IndexSel(x), (IndexSel(x_), subgoal) :: restgoals) if x == x_ => 
        ((pat, subgoal, subproof), restgoals)

      case (_, (sel, subgoal) :: restgoals) =>
        val (result, restgoals_) = match_subproof_to_subgoals(pat, subproof, restgoals)
        (result, (sel, subgoal) :: restgoals_)
        
    }

  def match_subproofs_to_subgoals(subproofs: List[(Sel, Proof)], subgoals: List[(Sel, Expr)]): (List[(Sel, Expr, Proof)], List[(Sel, Expr)]) = 
  subproofs match {
    case Nil =>
      (Nil, subgoals)

    case (pat, subproof) :: rest =>
      val (first_, subgoals_) = match_subproof_to_subgoals(pat, subproof, subgoals)
      val (rest_, subgoals__) = match_subproofs_to_subgoals(rest, subgoals_)
      (first_ :: rest_, subgoals__)
  }

  def apply(goal: Expr, tactic: Tactic, state: State, prover:Prover, rws: Map[Fun, List[Rule]]): List[(Sel, Expr)] = tactic match {
    case Induction(variable) =>
      induction(variable, goal, state)

    case Show(expr) => 
      val Clause(xs, ant, suc) = goal
      val goal_ = Clause(xs, expr::ant, suc)
      
      List(
        ProofSel -> expr,
        ThenSel -> goal_
      )   

    case Unfold(target , places) => 
      unfold(goal, target, places, state)
    
    case Auto => 
      val subgoal: Expr = prover.reduce(goal, state)
      if(subgoal == True) Nil else List(ProofSel -> subgoal)

    case BreakPoint =>
      val input = StdIn.readLine(s"\nbreakpoint: ${goal} >")
      List(ProofSel -> goal)
    
    case Sorry => Nil

    case Split => 
      val goals = Horn.assume(List(goal), Nil, Nil, Nil, Nil)
      println(goals.length)
      goals.zipWithIndex map{case (expr, i) => (IndexSel(i), expr)}
  }


  def apply(goal: Expr, proof: Proof, state: State, prover: Prover, rws: Map[Fun, List[Rule]]): Attempt = proof match {
    case Proof(tactic, subproofs) =>
      val subgoals = apply(goal, tactic, state, prover, rws)
      val (found, rest) = match_subproofs_to_subgoals(subproofs, subgoals)
      val prems_found = found map { 
        case (sel, expr, proof) => 
          val next = apply(expr, proof, state, prover, rws)
          (sel, Step(expr, 0, List(next)))
      }
      val prems_rest = rest map { //no proof parsed 
        case (sel, expr) if tactic != Auto =>
          val next = apply_auto(expr, state, prover, rws)
          (sel, Step(expr, 0, List(next)))
        
        case (sel, expr) => 
          (sel, Step(expr))
      }
      Attempt(tactic, prems_found ++ prems_rest)
  }

  def apply_auto(goal: Expr, state: State, prover: Prover, rws: Map[Fun, List[Rule]]) = {
    val goal__ = prover.reduce(goal, state)
    if(goal__ == True) Attempt(Auto, Nil) else Attempt(Auto, List(ProofSel -> Step(goal__)))
  }

  def induction(variable: Var, goal: Expr, state: State): List[(Sel, Expr)] = {
    require(!goal.isAtomic)
    val Sort(con, args) = variable.typ.asInstanceOf[Sort]
    val dt = state.datatypes(con.name)

    InductiveProver.induction(goal, variable, dt)
  }


  def unfold(goal: Expr, target: (Name, Int), places: Option[List[BigInt]], state: State): List[(Sel, Expr)] = {
    var i = 0

    val goal_ = goal.topdown {
    case e @ App(inst, args) if (inst.fun.name, args.length) == target =>
      i += 1

      if (places.isDefined && !places.get.contains(i)) {
        e
      } else {
        val (params, body) = state.fundefs(target)
        val su = params.zip(args).toMap
        body.subst(su)
      }

    case e =>
      e
    }
    List((ThenSel, goal_))
  }
}
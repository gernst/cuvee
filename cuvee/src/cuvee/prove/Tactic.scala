package cuvee.prove

import cuvee.pure.Fun
import cuvee.pure._
import cuvee.sub
import cuvee.pure.True
import cuvee.State
import cuvee.util.Name
import cuvee.smtlib._
import cuvee.pipe.Stage
import cuvee.iprove
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

case class IndexSel(index: Int) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case IndexSel(index_) => index_ == index
    case _ => false 
  }

  override def toString = "case " + index + " => "
}

trait Tactic {}
class TacticNotApplicableException(s: String) extends Exception(s) {}

case class Induction(x: Var) extends Tactic
case class Show(expression: Expr) extends Tactic
case class Unfold(target: (Name, Int), places: Option[List[BigInt]]) extends Tactic
case object NoAuto extends Tactic
case object Auto extends Tactic
case object BreakPoint extends Tactic
case object Sorry extends Tactic



// as written in input file
case class Proof(tactic: Tactic, subproofs: List[(Sel, Proof)])

object ProofUtils{

  def match_subproof_to_subgoals(pat: Sel, subproof: Proof, subgoals: List[(Sel, Expr)]): ((Sel, Expr, Proof), List[(Sel, Expr)]) = 
    (pat, subgoals) match {
      case (_, Nil) =>
        ???

      case (ConstrSel(sel, vars), (ConstrSel(sel_, vars_), subgoal) :: restgoals) if sel == sel_ =>
        val re = Expr.subst(vars_, vars)
        //val subgoal__ = subgoal rename re println(subgoal__)
        val Clause(xs, ant, suc) = subgoal
        val subgoal_ = Clause(xs rename re, ant rename re, suc rename re)
        ((pat, subgoal_, subproof), restgoals)

      case (ThenSel, (ThenSel, subgoal) :: restgoals) =>
        ((pat, subgoal, subproof), restgoals)

      case (ProofSel, (ProofSel, subgoal) :: restgoals) => 
        ((pat, subgoal, subproof), restgoals)

      case (IndexSel(x), (IndexSel(x_), subgoal) :: restgoals) if x == x_ => 
        ((pat, subgoal, subproof), restgoals)

      case (_, (sel, subgoal) :: restgoals) => // otherwise, maybe pat = nil does not match
        val (result, restgoals_) = match_subproof_to_subgoals(pat, subproof, restgoals)
        (result, (sel, subgoal) :: restgoals_) // keep the unmatched goal!
        
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

  def apply(goal: Expr, tactic: Tactic, state: State, cmds: List[Cmd]): List[(Sel, Expr)] = tactic match {
    case Induction(variable) =>
      induction(variable, goal, state)

    case Show(expr) => 
      //TODO ib replace check whether goal is Disj??? 
      //TODO without clause
      val Clause(xs, ant, suc) = goal
      val goals = Horn.assume(List(expr), Nil, xs, ant, List(suc))
      val goal_ = 
        if(goals.isEmpty) True 
        else And(goals)
      
      List(
        (ProofSel, expr), 
        (ThenSel, goal_)
      )   

         
    case Unfold(target , places) => 
      unfold(goal, target, places, state)
    
    case Auto => 
      val solver = Solver.z3()
      //initialize solver
      val cmds_ = cmds.dropRight(1)
      for(cmd <- cmds_){
        solver.exec(cmd, state)
      }
      val prover = Prover.fromSolver(solver, true)
      val subgoal: Expr = prover.reduce(goal, state)
      
      if(subgoal == True) Nil else List((ProofSel, subgoal))

    case BreakPoint =>
      val input = StdIn.readLine(s"\nbreakpoint: ${goal} >")
      List((ProofSel, goal))
    
    case Sorry => Nil

    case NoAuto => List((ProofSel, goal))

  }


  def apply(goal: Expr, proof: Proof, state: State, cmds: List[Cmd]): Attempt = proof match {
    case Proof(tactic, subproofs) =>
      val subgoals = apply(goal, tactic, state, cmds)
      val (found, rest) = match_subproofs_to_subgoals(subproofs, subgoals)
      val prems_found = found map { 
        case (sel, expr, proof) => 
          val next = apply(expr, proof, state, cmds)
          (sel, Step(expr, 0, List(next)))
      }
      val prems_rest = rest map { //no proof parsed 
        case (sel, expr) => (sel, Step(expr, -1, Nil))
      }
      Attempt(tactic, prems_found ++ prems_rest)
  }

  @throws[TacticNotApplicableException](
    "if the tactic is not applicable to the given goal and state"
  )
  def makesProgress(state: State, goal: Expr, tactic: Tactic, cmds: List[Cmd])(implicit
      prover: Prover
  ): Option[Int] = tactic match {
    case Induction(variable) => {
      val sort = variable.typ.asInstanceOf[Sort]
      val dt = state.datatypes
        .get(sort.con.name)
        .getOrElse(
          throw new TacticNotApplicableException(
            f"Can't apply induction to variable $variable, as it has no associated data type"
          )
        )

      val su = dt.params.zip(sort.args).toMap
      val insts = dt.constrs map (c => Inst(c._1, su))

      // Determine the non-recursive constructors and their indices in the list of generated cases
      val baseCases = insts.zipWithIndex.filterNot { case (i, _) =>
        i.args.contains(i.res)
      }

      // Check whether the goals of all resulting base cases can be proved automatically
      val baseIndices = baseCases map (_._2)

      // Apply the tactic
      val goals = apply(goal, tactic, state, cmds)
      val baseGoals = baseIndices map (goals(_))

      val success = baseGoals forall { case (goal, _) =>
        ???
        // Proving.proveAndSimplify(goal, prover, state) == Atom.t
      }

      success match {
        case true =>
          // Determine the progress we've made
          // As we know that the base cases can be proven automatically, the remaining complexity is given only by the remaining cases
          val originalComplexity = Rating.complexity(goal)
          val remainingComplexity = goals.zipWithIndex
            .filterNot(baseIndices.contains)
            .map(p => Rating.complexity(p._1._2))
            .max

          Some(originalComplexity - remainingComplexity)
        case _ => None
      }
    }

    case Unfold(target, places) => {
      
      val result = apply(goal, tactic, state, cmds)
      // We know that the applying the tactic yields exactly one subgoal (see above)
      val new_goal = result.head._2
      val goal_p = prover.reduce(new_goal, null)

      val diff = Rating.size(new_goal)(state) - Rating.size(goal_p)(state)

      if (diff > 0)
        Some(diff)
      else
        None
    }

    case _ => {
      val orig = Rating.complexity(goal)
      val cases = apply(goal, tactic, state, cmds)

      val snew = cases.map(c => Rating.complexity(c._2)).max

      if (snew < orig)
        Some(orig - snew)
      else
        None
    }
  }



  def induction(variable: Var, goal: Expr, state: State): List[(Sel, Expr)] = {
    goal match{
      case Forall(xs, _) if !(xs.contains(variable)) => 
        throw new TacticNotApplicableException(
          f"Can't apply induction to variable $variable, as it is not bound by topmost quantifier"
        )
      case _ if goal.isAtomic => 
        throw new TacticNotApplicableException(
          "Atom not supported in induction tactic, got:" + goal
        )
      case _ => ()
    }

    // First determine the variable's datatype
    val sort = variable.typ.asInstanceOf[Sort]
    val dt = state.datatypes
      .get(sort.con.name)
      .getOrElse(
        throw new TacticNotApplicableException(
          f"Can't apply induction to variable $variable, as it has no associated data type"
        )
      )

    assert(dt.params.length == sort.args.length)
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



  def insertAttempt(path: List[Sel], tree: Step, attempt: Attempt): Step = (path, tree.attempts) match {
    case (Nil, _) => Step(tree.goal, 0, attempt :: tree.attempts) //insert 
    
    case (head :: next, Nil) =>  tree
        
    case (head:: next, _ :: _) => 
      val attempt_curr = tree.attempts(tree.current)
      val updated_attempt = insertAttempt(path, attempt_curr) 
      Step(tree.goal, tree.current, tree.attempts.updated(tree.current, updated_attempt))
  }

  def insertAttempt(path: List[Sel], attempt: Attempt): Attempt = path match{
    case Nil =>  ??? //should not happen
    case sel_curr :: sel_rest => 
      val subgoals = attempt.prems
      val updatedPrems = for((sel, step) <- subgoals) yield{
        if(sel.matches(sel_curr)) (sel, insertAttempt(sel_rest, step, attempt))
        else (sel, step)
      }
      Attempt(attempt.tactic, updatedPrems)
  }

  def redoAttempt(path: List[Sel], tree: Step, direction: Int): Step = 
    (path, tree.attempts) match {
      case (_, Nil) => tree 
      
      case (Nil, _ :: _) => 
        val curr_attempts = tree.attempts
        val len = curr_attempts.length
        val nextIndex = (tree.current + direction) % len
        val nextIndexPos = if(nextIndex >= 0) nextIndex else nextIndex + len
        Step(tree.goal, nextIndexPos, tree.attempts)
      
      case (head :: tail, _ :: _) => 
        val attempt_curr = tree.attempts(tree.current)
        val updated_attempt = redoAttempt(path, attempt_curr, direction) 
        Step(tree.goal, tree.current, tree.attempts.updated(tree.current, updated_attempt))
    }

  def redoAttempt(path: List[Sel], attempt: Attempt, direction: Int): Attempt = path match{
    case Nil =>  ??? //should not happen
    case sel_curr :: sel_rest => 
      val subgoals = attempt.prems
      val updatedPrems = 
        for((sel, step) <- subgoals) yield{
          if(sel.matches(sel_curr)) 
            (sel, redoAttempt(sel_rest, step, direction))
          else 
            (sel, step)
        }
      Attempt(attempt.tactic, updatedPrems)
  }
}
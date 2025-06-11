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

trait Sel{
  def matches(sel: Sel): Boolean
}

case class ConstrSel(constructor: Fun, variables: List[Var]) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case ConstrSel(cons, vars) => 
      cons == constructor
    case _ => false
  }
}

case object ProofSel extends Sel{
  def matches(sel: Sel): Boolean = sel == ProofSel
}

case object ThenSel extends Sel{
    def matches(sel: Sel): Boolean = sel == ThenSel
}

case class IndexSel(index: Int) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case IndexSel(index_) => index == index
    case _ => false 
  }
}

trait Tactic {}
class TacticNotApplicableException(s: String) extends Exception(s) {}

case class Induction(x: Var) extends Tactic
case class Show(expression: Expr) extends Tactic
case class Unfold(target: (Name, Int), places: Option[List[BigInt]]) extends Tactic
case object NoAuto extends Tactic
case class SimpleProver2() extends Tactic
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
        println(subgoal_)
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
    
      val Clause(xs, ant, suc) = goal
      //TODO without clause
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

    case BreakPoint => List((ProofSel, goal))
    
    case Sorry => Nil

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
    List((ProofSel, goal_))
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

case class Step(goal: Expr, current: Int = -1, attempts: List[Attempt] = Nil){
  def closed : Boolean = {
    if(attempts.isEmpty) false
    else attempts(current).closed
  }

  def toString(offset: String = ""): String = {
    if(attempts.isEmpty) offset + goal.toString
    else offset + goal.toString + attempts(current).toString(offset + "   ")
  }

  def leaves : List[Expr] = {
    if(attempts.isEmpty) List(goal)
    else attempts(current).leaves
  }
}

case class Attempt(tactic: Tactic, prems: List[(Sel, Step)]){
  def closed : Boolean = prems.forall(_._2.closed)

  def toString(offset: String = ""): String = {
    offset + tactic.toString + "\n" + prems.map{case (sel, step) => step.toString(offset + "   ") + "\n"}
  }

  def leaves : List[Expr] = {
    prems flatMap {case (sel, step) => step.leaves}
  }
}

class Test(
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
        for (goal_ <- reduce(goal, tactic, rws, state, cmds) if !(goal_ == True))
          yield {
            println(goal_)
            val expr_ = goal_
            Lemma(expr_, None, Some(Goal), label)
          }

      case cmd @ Lemma(expr, tactic, None, label) =>
        val goal = expr
        for (goal_ <- reduce(goal, tactic, rws, state, cmds))
          yield {
            println(goal_)
            val expr_ = goal_
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
        for (goal_ <- reduce(goal, None, rws, state, cmds))
          yield {
            val expr_ = goal_
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
  ): List[Expr] = {
    val proof_cont = proof match{
      case None => Proof(Auto, Nil)
      case Some(value) => value
    }
    print(cuvee.boogie.Printer.proof(proof_cont))
    val attempt = ProofUtils.apply(goal, proof_cont, state, cmds)
    val tree = ProofUtils.insertAttempt(Nil, Step(goal, -1, Nil), attempt)
    println(tree.closed)
    tree.leaves
  }
}
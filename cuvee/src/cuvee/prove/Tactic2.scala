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

case class ConstructorSelector(constructor: (Fun, List[Fun]), variables: List[Var]) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case ConstructorSelector(cons, vars) => 
      cons._1.name == constructor._1.name //TODO ib is constructor name unique enough? 
    case _ => false
  }
}

case object ProofSelector extends Sel{
  def matches(sel: Sel): Boolean = sel eq ProofSelector
}

case object ThenSelector extends Sel{
    def matches(sel: Sel): Boolean = sel eq ThenSelector
}

case class IndexSelector(index: Int) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case IndexSelector(index_) => index_ == index 
    case _ => false
  }
}

trait Tactic2 {}
case class Induction2(x: Var) extends Tactic2
case class Show2(expression: Expr) extends Tactic2
case class Unfold2(target: (Name, Int), places: Option[List[BigInt]]) extends Tactic2
case object Auto2 extends Tactic2
case object Sorry2 extends Tactic2
case class Simplify2(rw: Map[Fun, List[Rule]]) extends Tactic2
case object BreakPoint extends Tactic2

// as written in input file
case class Proof(tactic: Tactic2, subproofs: List[(Sel, Proof)])

object ProofUtils{
  def match_subproof_to_subgoals(pat: Sel, subproof: Proof, subgoals: List[(Sel, Expr)]): ((Sel, Expr, Proof), List[(Sel, Expr)]) = {
    subgoals match {
      case Nil => ???

      case (sel, subgoal) :: restgoals =>
        // try match pat against sel, to get some mapping
        val success = sel.matches(pat)
        if(success)  { // match succeeded
          sel match{
            case ConstructorSelector(constructor, variables) =>
              val ConstructorSelector(pat_constr, pat_vars) = pat
              val (constr, consel) = constructor
              val su : Map[Var, Var] =
                (for ((variable, i) <- variables.zipWithIndex)
                yield{
                  val pat_var: Var = pat_vars(i)
                  assert(pat_var.typ == variable.typ)
                  (variable, pat_var)
                }).toMap
              
              val Clause(xs, ant, suc) = subgoal
              val subgoal_ : Expr = Clause(xs rename su, ant rename su, suc rename su)
              ((pat, subgoal_, subproof), restgoals)
            case _ => ((pat, subgoal, subproof), restgoals)
          }  
        } else { // otherwise, maybe pat = nil does not match
            val (result, restgoals_) = match_subproof_to_subgoals(pat, subproof, restgoals)
            (result, (sel, subgoal) :: restgoals_) // keep the unmatched goal!
        }
    }
  }

  def match_subproofs_to_subgoals(subproofs: List[(Sel, Proof)], subgoals: List[(Sel, Expr)]): (List[(Sel, Expr, Proof)], List[(Sel, Expr)]) = {
    subproofs match {
      case Nil =>
        (Nil, subgoals)

      case (pat, subproof) :: rest =>
        val (first_, subgoals_) = match_subproof_to_subgoals(pat, subproof, subgoals)
        val (rest_, subgoals__) = match_subproofs_to_subgoals(rest, subgoals_)
        (first_ :: rest_, subgoals__)
    }
  }

  def apply(goal: Expr, tactic: Tactic2, state: State): List[(Sel, Expr)] = tactic match {
    case Induction2(variable) =>
      goal match{
        case Clause(xs, _, _) if !(xs.contains(variable)) => 
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

      val Clause(xs, ant, suc) = goal
      val Sort(con, args) = sort
      val Datatype(params, constrs) = dt
      val su: Map[Param, Type] = Type.subst(params, args)

      //goal without induction variable in top level
      val goal_ = Clause(xs.filterNot(_ == variable), ant, suc)
      
      val ind = 
        for ((constr, sels) <- constrs) yield {
          val args =
              for (Fun(name, _, _, res) <- sels)
              yield Expr.fresh(name, res subst su)

          val hyps = 
              for ((Var(_, Sort(con_, _)), i) <- args.zipWithIndex if con_ == con) 
              yield i
          
          (Inst(constr, su), args, hyps, ConstructorSelector((constr, sels), xs.filterNot(_ == variable) ++ args))
        }
  
      for ((constr, args, hyps, selector) <- ind) yield {
        val expr = App(constr, args)

        val prems = for (i <- hyps) yield {
          val y = args(i)
          val re = Map(variable -> y)

          Clause(
            xs filter (_ != variable),
            ant rename re,
            suc rename re
          )
        }

        val su = Map(variable -> expr)
        val new_goal = Clause(xs.filterNot(_ == variable) ++ args, prems ++ (ant subst su), suc subst su)
        
        (selector, new_goal)
      }  
    case Show2(expr) => 
      goal match {
          case Clause(xs, _, _) => ()
          case _ => throw new TacticNotApplicableException(
              f"Can't apply show to $goal"
            )
        } 
    
        val Clause(xs, ant, suc) = goal
    
        val goals = Horn.assume(List(expr), Nil, xs, ant, List(suc))
        val goal_ = 
          if(goals.isEmpty) True 
          else if(goals.length <= 1) goals.head 
          else throw new TacticNotApplicableException(f"assume created more goals than expected: $goals")
    
        List(
          (ProofSelector, expr), 
          (ThenSelector, goal_)
        )        
    case Unfold2(target , places) => 
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
      List((IndexSelector(0), goal_))
    case Auto2 => List((IndexSelector(0), goal)) //TODO ib call prover
    case Sorry2 => Nil
    case BreakPoint => List((IndexSelector(0), goal))
  }


  def apply(goal: Expr, proof: Proof, state: State): Attempt = proof match {
    case Proof(tactic, subproofs) =>
      val subgoals = apply(goal, tactic, state)
      val (found, rest) = match_subproofs_to_subgoals(subproofs, subgoals)
      val prems_found = found map { 
        case (sel, expr, proof) => 
          val next = apply(expr, proof, state)
          (sel, Step(expr, 0, List(next)))
      }
      val prems_rest = rest map { //no proof parsed 
        //TODO auto / call prover
        case (sel, expr) => (sel, Step(expr, -1, Nil))
      }
      Attempt(tactic, prems_found ++ prems_rest)
  }

  def insertAttempt(path: List[Sel], tree: Step, attempt: Attempt): Step = path match {
    case Nil => Step(tree.goal, 0, attempt :: tree.attempts) //insert 
    case head :: next => 
      tree.attempts match{
        case Nil => tree
        
        case _ :: _ => 
          val attempt_curr = tree.attempts(tree.current)
          val updated_attempt = insertAttempt(path, attempt_curr) 
          Step(tree.goal, tree.current, tree.attempts.updated(tree.current, updated_attempt))
      }
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

  def redoAttempt(path: List[Sel], tree: Step, direction: Int): Step = path match {
    case Nil => 
      val curr_attempts = tree.attempts
      if(curr_attempts.isEmpty) 
        tree
      else {
        val len = curr_attempts.length
        val nextIndex = (tree.current + direction) % len
        val nextIndexPos = if(nextIndex >= 0) nextIndex else nextIndex + len
        Step(tree.goal, nextIndexPos, tree.attempts)
      }
    
    case head :: tail => 
      if(tree.attempts.isEmpty) tree
      else{
        val attempt_curr = tree.attempts(tree.current)
        val updated_attempt = redoAttempt(path, attempt_curr, direction) 
        Step(tree.goal, tree.current, tree.attempts.updated(tree.current, updated_attempt))
      }
  }

  def redoAttempt(path: List[Sel], attempt: Attempt, direction: Int): Attempt = path match{
    case Nil =>  ??? //should not happen
    case sel_curr :: sel_rest => 
      val subgoals = attempt.prems
      val updatedPrems = for((sel, step) <- subgoals) yield{
        if(sel.matches(sel_curr)) (sel, redoAttempt(sel_rest, step, direction))
        else (sel, step)
      }
      Attempt(attempt.tactic, updatedPrems)
  }
}

case class Step(goal: Expr, current: Int = -1, attempts: List[Attempt] = Nil){
  def closed : Boolean = {
    if(attempts.isEmpty) false
    else attempts(current).closed
  }
}

case class Attempt(tactic: Tactic2, prems: List[(Sel, Step)]){
  def closed : Boolean = {
    if(prems.isEmpty) true
    else(prems.forall(_._2.closed))
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
        for (goal_ <- reduce(goal, tactic, rws, state) if !(goal_ == True))
          yield {
            println(goal_)
            val expr_ = goal_
            Lemma(expr_, None, Some(Goal), label)
          }

      case cmd @ Lemma(expr, tactic, None, label) =>
        val goal = expr
        for (goal_ <- reduce(goal, tactic, rws, state))
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
        for (goal_ <- reduce(goal, None, rws, state))
          yield {
            println(goal_)
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
    tactic: Option[Tactic],
    rws: Map[Fun, List[Rule]],
    state: State
  ): List[Expr] = {
    val tactic2: Tactic2 = tactic match{
      case None => Auto2
      case Some(Induction(variable, cont)) => Induction2(variable)
      case Some(Show(expr, proof, cont)) => Show2(expr)
      case Some(Auto) => Auto2 
      case Some(Sorry) => Sorry2
    }
    
    val proof_cont: List[(Sel, Proof)] = List((ThenSelector, Proof(Sorry2, Nil))) :+ (ProofSelector, Proof(Auto2, Nil))
    val attempt = ProofUtils.apply(goal, Proof(tactic2, proof_cont ), state)
    val tree = ProofUtils.insertAttempt(Nil, Step(goal, -1, Nil), attempt)
    println(attempt)
    /*
    val attempt = ProofUtils.apply(goal, Proof(BreakPoint, Nil), state)
    val tree = ProofUtils.apply(Nil, Step(goal, -1, Nil), attempt)
    */
    val tree2 = Step(goal, 0, List(Attempt(Sorry2, Nil)))
    println(tree2 + "\n" + tree2.closed)
    
    attempt.prems.map{case (sel, step) => step.goal}
  }
}
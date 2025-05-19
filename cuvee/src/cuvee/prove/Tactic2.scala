package cuvee.prove

import cuvee.pure.Fun
import cuvee.pure._
import cuvee.sub
import cuvee.pure.True
import cuvee.State
import cuvee.util.Name

trait Sel{
  def matches(sel: Sel): Boolean
}

case class ConstructorSelector(constructor: (Fun, List[Fun]), variables: List[Var]) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case ConstructorSelector(cons, vars) => cons._1.name == constructor._1.name
    case _ => false
  }
}

case object ProofSelector extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case ProofSelector => true
    case _ => false
  }
}

case object ThenSelector extends Sel{
    def matches(sel: Sel): Boolean = sel match{
    case ThenSelector => true
    case _ => false
  }
}

case class IndexSelector(index: Int) extends Sel{
  def matches(sel: Sel): Boolean = sel match{
    case IndexSelector(index) => true
    case _ => false
  }
}

trait Tactic2 {}
case class Induction2(x: Var) extends Tactic2
case class Show2(expression: Expr) extends Tactic2
case class Unfold2(target: (Name, Int), places: Option[List[BigInt]]) extends Tactic2
case object Auto2 extends Tactic2
case object Sorry2 extends Tactic2

// as written in input file
case class Proof(tactic: Tactic2, subproofs: List[(Sel, Proof)])

object ProofUtils{
  def match_subproof_to_subgoals(pat: Sel, subproof: Proof, subgoals: List[(Sel, Expr)]): ((Sel, Expr, Proof), List[(Sel, Expr)]) = {
    subgoals match {
      case Nil => throw new MatchError("cannot apply subproof")
        // cannot apply subproof


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
              
              // possy instantiate subgoal with this mapping, e.g.
              // pat = case cons(y, zs) =>
              // sel = case cons(head_0, tail_1) =>
              // subgoal = P(head_0, tail_1)
              // then compute renaming re = Map(y -> head_0, zs -> tail_1)
              // and subgoal_ = subgoal rename re
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
      //TODO ib
      // generate cases etc with fresh variables
      // List("nil" -> base_case, "cons(head_0, tail_1)" => recursive_case)
      // ensures that all selectors are "disjoint", i.e., there are no two subgoals that can be matched by the same selector later
    
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
          (ThenSelector, goal)
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
    
    case Auto2 => List((IndexSelector(0), goal))

    case Sorry2 => Nil

  }


  def apply(goal: Expr, proof: Proof, state: State): Attempt = proof match {
    case Proof(tactic, subproofs) =>
      val subgoals = apply(goal, tactic, state)
      val (found, rest) = match_subproofs_to_subgoals(subproofs, subgoals)
      val prems_found = found map {case (sel, expr, proof) => (sel, Step(expr, -1, Nil))} //TODO what to do with proof
      val prems_rest = rest map {case (sel, expr) => (sel, Step(expr, -1, Nil))}
      Attempt(tactic, prems_found) //TODO rest
  }

  def apply(path: List[Sel], tree: Step, attempt: Attempt): Step = path match {
    case Nil => Step(tree.goal, 0, attempt :: tree.attempts)
    case head :: next => 
      tree.attempts match{
        case Nil => ??? 
          //Step(tree.goal, tree.current, tree.attempts)
        
        case _ :: _ => 
          val attempt_curr = tree.attempts(tree.current)
          val updated_attempt = apply(path, attempt_curr, attempt)
          Step(tree.goal, tree.current, tree.attempts.updated(tree.current, updated_attempt))
      }
  }

  def apply(path: List[Sel], attempt: Attempt, new_attempt: Attempt): Attempt = {
    ???
  }
}

case class Step(goal: Expr, current: Int, attempts: List[Attempt])

case class Attempt(tactic: Tactic2, prems: List[(Sel, Step)])


package cuvee.iprove

import cuvee.State
import cuvee.pure._
import cuvee.prove.Prover
import cuvee.sexpr



sealed trait Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)]
}

class TacticNotApplicableException(s: String) extends Exception(s) {}


case class Induction(variable: Var, hyp: Boolean = true) extends Tactic{
    def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = {
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
      val cases: List[(Expr, cuvee.prove.Tactic)]  = Nil
      
      val con_tactics = cases
        .collect({ case (expr: App, tactic) =>
          (expr.inst, (expr, tactic))
        })
        .toMap
        
      val Clause(xs, ant, suc) = goal
      val Sort(con, args) = sort
      val Datatype(params, constrs) = dt
      val su: Map[Param, Type] = Type.subst(params, args)
        
      val ind = 
        for ((constr, sels) <- constrs) yield {
          val args =
            for (Fun(name, _, _, res) <- sels)
              yield Expr.fresh(name, res subst su)
  
          val hyps = 
            for ((Var(_, Sort(con_, _)), i) <- args.zipWithIndex if con_ == con) 
              yield i
          
          (Inst(constr, su), args, hyps)
        }
  
      for (((constr, args, hyps), index) <- ind.zipWithIndex) yield {
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
        
        (new_goal, index.toString)
      }
    }
}

case class Show(expr: Expr) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]) = {
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

    List((expr, "0"),
        (goal_, "1"))
  }   
}


case object Split extends Tactic{
  def apply(expr: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = {
    expr match{
      case _ if(expr.isAtomic) => if(expr == true) Nil else List((expr, "split"))
      //Disj := Expr /\ ... /\ Expr => Conj \/ ... \/ Conj
      case Clause(xs, assms, concls) => 
        //val subgoals = split(xs, assms, concls)
        val subgoals = List(expr)
        subgoals.zipWithIndex.map{case (goal, i) => (expr, i.toString())}
    }
  }

  /** 
   *  @return Conclusion A /\ B split into subgoals A, B
    * Conj := Expr /\ Expr
    * Expr := Atom | Disj
    * Disj := Expr /\ ... /\ Expr => Conj \/ ... \/ Conj
    *
    *  A && B => A, B
    * (A && (C || D)) => A, (C || D)
    * (A && B) || (C && D) => ((C && D) || A), ((C && D) || B)
    *                         ((C && D) || A) => (A || C), (A || D)
    * ((A || B) && C) => (A || B), C
    * (A && B) || C => ( C || A ), (C || B)
    */
  /*
  def split(xs: List[Var], assms: List[Expr],  concls: List[Conj]): List[Expr] = {
    
    var splitConcls: List[Expr] = concls.flatMap{concl => 
        concl.props match{
          case Nil => Nil
          case head :: Nil => Nil 
          case head :: tail => return List(Clause(xs, assms, concls.filterNot(_ == concl) :+ Exists(concl.xs, And(head)))) :+
                                    Clause(xs, assms, concls.filterNot(_ == concl) :+ Exists(concl.xs, And(tail)))
          }
        }    
    //splitConcls = splitConcls.toMap.toList
    if(splitConcls.isEmpty) List(Clause(xs, assms, concls)) else splitConcls
  }
    */
}

case class SelectGoal(nr: Int) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil 
}

case class Auto(prover: Prover) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = {
    val result = prover.apply(state, goal)
    assert(result.length == 1)
    val (goal_, _) = result.head
    println(goal_)
    if(goal_.equals(True)){
      Nil
    } 
    else{
      List((goal_, "fail"))
    }
  }
}

object Simplify extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = {
    val goal_ = cuvee.pure.Simplify.simplify(goal, rws, state.constrs)
    
    if(goal_.equals(True)) Nil else List((goal_, "simp"))
  }
}

case class Default(tactic: Tactic) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun,List[Rule]]): List[(Expr, String)] = {
    tactic.apply(goal, state, rws)
  }
}

object Sorry extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]) : List[(Expr, String)] = Nil
}

object Skip extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Exit extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

case class Undo(local: Boolean) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Redo extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Help extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Proof extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Up extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

case class SelectChild(nr: Int) extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Check extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object RwRules extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}

object Goal extends Tactic{
  def apply(goal: Expr, state: State, rws: Map[Fun, List[Rule]]): List[(Expr, String)] = Nil
}
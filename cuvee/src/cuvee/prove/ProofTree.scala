package cuvee.prove

import cuvee.State
import cuvee.pure._
import scala.io.StdIn
import cuvee.util.Name

case class Step(goal: Expr, current: Int = -1, attempts: List[Attempt] = Nil){
  def closed : Boolean = {
    if(attempts.isEmpty) false
    else attempts(current).closed
  }

  def toString(offset: Int = 0): String = {
    if(attempts.isEmpty) goal.toString
    else 
      goal.toString +
      attempts(current).toString(offset)
  }

  def leaves : List[Expr] = {
    if(attempts.isEmpty) List(goal)
    else attempts(current).leaves
  }
}

case class Attempt(tactic: Tactic, prems: List[(Sel, Step)]){
  def closed : Boolean = prems.forall(_._2.closed)

  def toString(offset: Int = 0): String = {
    var res = "\n" + "     " * offset + " [" + tactic.toString + "]"
    val rest =
      for ((sel, step) <- prems) {
        val add: Int = sel.toString.length / 5
        res += "\n" + "     " * offset + " |" + "___" + sel + step.toString(offset + 1 + add)
      }
    res
  }

  def leaves : List[Expr] = {
    prems flatMap {case (sel, step) => step.leaves}
  }

}

object TreeUtils{
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
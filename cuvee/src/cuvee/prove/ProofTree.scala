package cuvee.prove

import cuvee.pure.Expr


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
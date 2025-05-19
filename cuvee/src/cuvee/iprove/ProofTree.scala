package cuvee.iprove

import cuvee.pure.Expr

/*
sealed trait Branch

def apply(path: List[Int], tree: Tree, tactic: Tactic): Tree
def apply(expr: Expr, tactic: Tactic): List[(Branch, Expr)]

case class Attempt(tactic: Tactic, prems: List[(Branch,Tree)])
*/

sealed trait Tree{
  def name: String
  def index: Int
  def goal: Expr
  def attempts: List[Attempt]

  def isClosed: Boolean
  def results: List[Expr]
  def getOpen: List[(String, Expr)]
  def getOpenAt(name: String) : List[(String, Expr)]
  def getParent(name: String) : Option[(String, Expr)]
  def getChildrenAt(name: String) : List[(String, Expr)]
  def getTactic(name: String): Option[Tactic]
  def getGoal(name: String): Option[Expr]

  def newAttempt(name: String, subtrees: List[Tree], tactic: Tactic): Tree
  def undo(name: String): Tree
  def redo(name: String): Tree
}

case class Step(goal: Expr, attempts: List[Attempt], name: String, index: Int = -1) extends Tree{

  def isClosed: Boolean = {
    if(attempts.isEmpty) false
    else attempts(index).isClosed
  }

  def results: List[Expr] = {
    if(attempts.isEmpty || attempts(index).tactic == Skip) List(goal)
    else attempts(index).results
  }

  def getOpen: List[(String, Expr)] = {
    if(attempts.isEmpty || attempts(index).tactic == Skip) List((name, goal)) 
    else attempts(index).getOpen
  }

  def getOpenAt(name: String): List[(String, Expr)] = {
    if(attempts.isEmpty) Nil
    else if(name == this.name) this.getOpen
    else attempts(index).prems flatMap {prem => prem.getOpenAt(name)}
  }

  def getChildrenAt(parent: String): List[(String, Expr)] = {
    if(attempts.isEmpty) Nil
    else if(parent == this.name) attempts(index).prems map (prem => (prem.name, prem.goal))
    else attempts(index).prems flatMap {prem => prem.getChildrenAt(parent)}
  }

  def getParent(child: String): Option[(String, Expr)] = {
    if(attempts.isEmpty) None
    else if(attempts(index).hasChild(child))
      Some((this.name, goal))
    else{ 
      var results = attempts(index).prems map (prem => prem.getParent(child))
      results = results.filter(_ != None)
      if(results.isEmpty) None
      else results.head
    }
  }

  def getTactic(name: String): Option[Tactic] = {
    if(attempts.isEmpty) None
    else if (name == this.name) Some(attempts(index).tactic)
    else {
      var tactics = attempts(index).prems map {prem => prem.getTactic(name)}
      tactics = tactics.filter(_ != None)
      if(tactics.isEmpty) None 
      else tactics.head
    }
  }

  def getGoal(name: String): Option[Expr] = {
    if(name == this.name) Some(goal)
    else if(attempts.isEmpty) None
    else{
      var matches = attempts(index).prems map {
        prem => prem.getGoal(name)
      }
      matches = matches.filter(_ != None)
      if(matches.isEmpty) None
      else matches.head
    }
  }

  /**
    * replaces first attempt in the attempts - replaces a "skip" tactic or is added to empty list.
    * if an identical tactic already exists in the attempts list, this attemps is restored instead. 
    * Attempts are stored chronologically
    * 
    * @param name name of subgoal a tactic was applied to
    * @param subtrees the subgoals created by the tactic in a Tree object
    * @param tactic the applied tactic
    * @return the updated Tree Object
    */
  def newAttempt(name: String, subtrees: List[Tree], tactic: Tactic): Tree = 
    if(this.name == name) {
      val attempt = Attempt(tactic, subtrees)
      if(attempts.isEmpty) Step(goal, List(attempt), this.name, 0)
      else {
        assert(attempts.head.tactic == Skip)
        Step(goal, attempt +: attempts.tail.filterNot(_ == attempt), this.name, 0)
      }
    }
    else if(!attempts.isEmpty) {
      val currentAttempt = attempts.apply(index)
      val updatedAttempt = currentAttempt.newAttempt(name, subtrees, tactic)
      Step(goal, attempts.updated(index, updatedAttempt), this.name, index)
    }
    else this
  
   /**
     * adds a new empty / "skip" attempt to the front of the attempts list and moves the pointer there
     * (Attempts are stored chronologically)
     * @param name name of subgoal undo was called on
     * @return the updated Tree
     */
  def undo(name: String): Tree = 
    if(this.name == name){
      val attempt = Attempt(Skip, Nil)
      Step(this.goal, attempt +: attempts.filter(_.tactic != Skip), this.name, 0)
    }
    else if(!attempts.isEmpty) {
      val updatedAttempt = attempts(index).undo(name)
      Step(goal, attempts.updated(index, updatedAttempt), this.name, index)
    }
    else this
  
  /**
    * Restores the last attempt behind the current by moving the pointer one further down the list.
    * Overflows to the first element in the list
    * (Attempts are stored chronologically)
    * @param name name of subgoal redo was called on
    * @return the updated Tree
    */
  def redo(name: String): Tree = 
    if(this.name == name && !attempts.isEmpty){
      val newIndex = (index + 1) % attempts.length
      Step(this.goal, this.attempts, this.name, newIndex)
    }
    else if(!attempts.isEmpty){
      val currentAttempt = attempts.apply(index)
      val updatedAttempt = currentAttempt.redo(name)
      Step(goal, attempts.updated(index, updatedAttempt), this.name, index)
    }
    else this
}


case class Attempt(tactic: Tactic, prems: List[Tree]){
  def newAttempt(name: String, subtrees: List[Tree], tactic: Tactic): Attempt =
    Attempt(this.tactic, prems map {prem => prem.newAttempt(name, subtrees, tactic)})

  def undo(name: String) : Attempt = 
    Attempt(tactic, prems map {prem => prem.undo(name)})

  def redo(name: String) : Attempt = Attempt(tactic, prems map {prem => prem.redo(name)})

  def hasChild(name: String) : Boolean = prems.exists(_.name == name)

  def isClosed: Boolean = {
    if(prems.isEmpty && tactic != Sorry) false
    else prems.forall(_.isClosed)
  }

  def results: List[Expr] = {
    if(prems.isEmpty) Nil
    else prems flatMap {prem => prem.results} 
  }

  def getOpen: List[(String, Expr)] = {
    prems flatMap {prem => prem.getOpen}
  }

}
/* 
package cuvee.prove

import scala.annotation.varargs
import scala.language.postfixOps

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Name
import cuvee.prove.Rating
import cuvee.pure.Quant.forall

/** Represents an instance of a tactic, possibly with arguments.
  * 
  * An instance of this trait may be applied to a proof obligation.
  */
trait Tactic {

  /** Apply the tactic to a proposition in a given state
    *
    * @param state
    * @param goal
    * @return
    *   A list of subgoals, given as tuples (prop, tactic?), where prop is the
    *   formula corresponding to the subgoal and tactic? is an optional tactic
    *   to prove the subgoal.
    */
  @throws[TacticNotApplicableException](
    "if the tactic is not applicable to the given goal and state"
  )
  def apply(state: State, goal: Expr): List[(Expr, Option[Tactic])]

  // TODO da: Does the current implementation work for most / some cases?
  /** Heuristic that tries to determine whether a tactic application that
    * produced the given `cases` made progress.
    *
    * When the application is deemed successful, this method returns
    *
    * This default implementation only measures whether the sum of the cases'
    * complexities is strictly lower than the complexity of the original goal.
    */
  
}

/** A trait that allows some implementation to suggest a tactic that may be
  * applied to a given goal in a given state.
  */
trait Suggest {

  /** Suggest some tactics that could be applied for the given `state` and
    * `goal`
    *
    * @param state
    * @param goal
    * @return
    *   List of tactics that are applicable for the given state and goal
    */
  def suggest(state: State, goal: Expr): List[Tactic]

  /** Suggest some tactics that could be automatically applied for the given
    * `state` and `goal`.
    *
    * By default, this returns the same tactics as `suggest`.
    *
    * @param state
    * @param goal
    * @return
    *   List of tactics that are applicable for the given state and goal
    */
  def suggestAuto(state: State, goal: Expr): List[Tactic] = suggest(state, goal)
}

object Suggest extends Suggest {
  val suggesters: List[Suggest] = List(Induction, Unfold)

  def suggest(state: State, goal: Expr): List[Tactic] = goal match {
    case True | False => Nil
    case goal            => suggesters flatMap (_.suggest(state, goal))
  }

  override def suggestAuto(state: State, goal: Expr): List[Tactic] = goal match {
    case True | False => Nil
    case goal            => suggesters flatMap (_.suggestAuto(state, goal))
  }
}

class TacticNotApplicableException(s: String) extends Exception(s) {}

object Induction
    extends ((Var, List[(Expr, Tactic)]) => Induction)
    with Suggest {

  def suggest(state: State, goal: Expr): List[Tactic] = goal match {
    case Clause(xs, neg, pos) =>
      for (x <- xs if getDatatype(x)(state).isDefined)
        yield Induction(x, Nil)
    case _ => Nil
  }

  def getDatatype(variable: Var)(implicit state: State): Option[Datatype] = {
    val sort = variable.typ.asInstanceOf[Sort]
    state.datatypes.get(sort.con.name)
  }
}


object Unfold
    extends (((Name, Int), Option[List[BigInt]], Option[Tactic]) => Unfold)
    with Suggest {

  /** Suggest to unfold definitions.
    *
    * This function produces suggestions for unfolding definitions.
    * If a function / constant occurs more than once in the goal, unfolding
    * every ocurrence is suggested, as well as unfolding all occurrences.
    *
    * @param state
    * @param goal
    * @return
    */
  def suggest(state: State, expr: Expr): List[Tactic] = {
    // First, find all unfoldable functions in the goal
    var functions = collection.mutable.Map[(Name, Int), Int]()

    expr.topdown {
      case app @ App(inst, args)
          if state.fundefs.contains((inst.fun.name, args.length)) => {
        val name = inst.fun.name
        val arity = args.length
        val (_, body) = state.fundefs((name, arity))

        // In case of a recursive definition, bail out
        if (!body.funs.contains(inst.fun))
          functions.update((name, arity), functions.getOrElse((name, arity), 0) + 1)

        app
      }
      case e => e
    }

    // Generate the tactic suggestions for the unfoldable functions
    functions.flatMap { case (fn, cnt) =>
      if (cnt == 1)
        List(Unfold(fn, Some(List(1)), None))
      else
        (1 to cnt).map(i => 
          Unfold(fn, Some(List(i)), None)
        ) :+ Unfold(fn, None, None)
    }.toList
  }

  /** Suggest definitions to automatically unfold.
    *
    * Here we reduce the suggestions from `suggest` to those, in which we have a
    * predicate that we unfold.
    *
    * @param state
    * @param goal
    * @return
    */
  override def suggestAuto(state: State, goal: Expr): List[Tactic] = {
    val suggestions = suggest(state, goal) map (t => t.asInstanceOf[Unfold])
    // At this point we know that the function exists, so we can request the definition from the state
    // and filter for unfodings of predicates
    suggestions filter (t => state.funs(t.target).res == Sort.bool)
  }
}

 */
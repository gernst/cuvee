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
  def makesProgress(state: State, goal: Expr)(implicit
      prover: Prover
  ): Option[Int] = {
    val orig = Rating.complexity(goal)
    val cases = apply(state, goal)

    val snew = cases.map(c => Rating.complexity(c._1)).max

    if (snew < orig)
      Some(orig - snew)
    else
      None
  }
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

case object Sorry extends Tactic {
  def apply(state: State, goal: Expr) = {
    // Currently a no-op
    println("\u001b[93m⚠\u001b[0m Use of the \u001b[93msorry\u001b[0m tactic!")
    Nil
  }
}

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

case class Induction(variable: Var, cases: List[(Expr, Tactic)]) extends Tactic {

  def apply(state: State, goal: Expr) = {
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
    
    val con_tactics = cases
      .collect({ case (expr: App, tactic) =>
        (expr.inst, (expr, tactic))
      })
      .toMap
      
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
        
        (Inst(constr, su), args, hyps)
      }

    for ((constr, args, hyps) <- ind) yield {
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
      val new_goal = Clause(xs ++ args, prems ++ (ant subst su), suc subst su)
      
      (new_goal, con_tactics.get(constr) map (_._2))
    }
  }

  override def makesProgress(
      state: State,
      goal: Expr
  )(implicit
      prover: Prover
  ): Option[Int] = {
    // Determine the variable's datatype
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
    val goals = apply(state, goal)
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
          .map(p => Rating.complexity(p._1._1))
          .max

        Some(originalComplexity - remainingComplexity)
      case _ => None
    }
  }
}

case class Show(
    expr: Expr,
    tactic: Option[Tactic],
    cont: Option[Tactic]
) extends Tactic {
  def apply(state: State, goal: Expr) = {
    goal match {
      case Clause(xs, _, _) => ()
      case _ => throw new TacticNotApplicableException(
          f"Can't apply show to $goal"
        )
    } 

    val Clause(xs, ant, suc) = goal

    val goals = Horn.assume(List(expr), Nil, xs, ant, List(suc))
    assert(goals.length == 1)
    val goal_ = goals.head

    List(
      (expr, tactic), //TODO replace from?
      (goal_, cont)
    )
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

case class Unfold(
    target: (Name, Int),
    places: Option[List[BigInt]],
    cont: Option[Tactic]
) extends Tactic {
  require(!places.isDefined || places.get.forall(i => 1 <= i))

  def apply(state: State, expr: Expr) = {
    var i = 0

    val goal_ = expr.topdown {
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
    //TODO replaced from
    List((goal_, cont))
  }

  override def makesProgress(state: State, goal: Expr)(implicit prover: Prover): Option[Int] = {
    // Tentatively apply every suggested unfolding of predicates
    val result = apply(state, goal)
    // We know that the applying the tactic yields exactly one subgoal (see above)
    val new_goal = result.head._1
    val goal_p = prover.reduce(new_goal, null)

    val diff = Rating.size(new_goal)(state) - Rating.size(goal_p)(state)

    if (diff > 0)
      Some(diff)
    else
      None
  }
}

/** This "tactic" only returns the original goal with no tactic.
  * It can be used to make it explicit, where goals shall be closed automatically.
  *
  * @param tactic
  */
object Auto extends Tactic {

  def apply(state: State, goal: Expr): List[(Expr, Option[Tactic])] =
    List((goal, None))
}


/** This "tactic" is actually just a wrapper for another tactic. It serves to
  * signal that no automatic proving attempt shall happen, before the contained
  * tactic has been applied.
  *
  * @param tactic
  */
case class NoAuto(tactic: Tactic) extends Tactic {

  def apply(state: State, goal: Expr): List[(Expr, Option[Tactic])] =
    tactic.apply(state, goal)
}

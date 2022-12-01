package cuvee.backend

import scala.annotation.varargs
import scala.language.postfixOps

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Name
import cuvee.util.Rating
import cuvee.util.Proving

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
  def apply(state: State, goal: Prop): List[(Prop, Option[Tactic])]

  // TODO da: Does the current implementation work for most / some cases?
  /** Heuristic that tries to determine whether a tactic application that
    * produced the given `cases` made progress.
    *
    * When the application is deemed successful, this method returns
    *
    * This default implementation only measures whether the sum of the cases'
    * complexities is strictly lower than the complexity of the original goal.
    */
  def makesProgress(state: State, goal: Prop)(implicit
      prover: Prove
  ): Option[Int] = {
    val orig = Rating.complexity(goal)
    val cases = apply(state, goal)

    val snew = cases.map(c => Rating.complexity(c._1)).sum

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
  def suggest(state: State, goal: Prop): List[Tactic]
}

object Suggest extends Suggest {
  val suggesters: List[Suggest] = List(Induction, Unfold)

  def suggest(state: State, goal: Prop): List[Tactic] = goal match {
    case Atom.t | Atom.f => Nil
    case goal            => suggesters flatMap (_.suggest(state, goal))
  }
}

class TacticNotApplicableException(s: String) extends Exception(s) {}

case class Builtin(rules: Map[Fun, List[Rule]], solver: Solver) extends Tactic {

  def apply(state: State, goal: Prop) = {
    val goal_ = Simplify.simplify(goal, rules)

    goal_ match {
      case Atom.t =>
        Nil
      case Atom.f =>
        throw new TacticNotApplicableException("not solvable")
      case _ =>
        List(goal -> None)
    }
  }
}

case object Sorry extends Tactic {

  def apply(state: State, goal: Prop) = {
    // Currently a no-op
    println("\u001b[93m⚠\u001b[0m Use of the \u001b[93msorry\u001b[0m tactic!")
    Nil
  }
}

object Induction
    extends ((Var, List[(Expr, Tactic)]) => Induction)
    with Suggest {

  def suggest(state: State, goal: Prop): List[Tactic] = goal match {
    case Disj(xs, neg, pos) =>
      for (x <- xs if getDatatype(x)(state).isDefined)
        yield Induction(x, Nil)
    case _ => Nil
  }

  def getDatatype(variable: Var)(implicit state: State): Option[Datatype] = {
    val sort = variable.typ.asInstanceOf[Sort]
    state.datatypes.get(sort.con.name)
  }
}

case class Induction(variable: Var, cases: List[(Expr, Tactic)])
    extends Tactic {

  def apply(state: State, goal: Prop) = {
    goal match {
      case Atom(_, _) | Conj(_, _) =>
        throw new TacticNotApplicableException(
          "Only Disj supported in induction tactic"
        )
      case Disj(xs, _, _) if !(xs contains variable) =>
        throw new TacticNotApplicableException(
          f"Can't apply induction to variable $variable, as it is not bound by topmost quantifier"
        )
      case _ => ()
    }

    // First determine the variable's datatype
    val sort = variable.typ.asInstanceOf[Sort]
    val dt = Induction.getDatatype(variable)(state).getOrElse(
                throw new TacticNotApplicableException(f"Can't apply induction to variable $variable, as it has no associated data type"))

    assert(dt.params.length == sort.args.length)
    val su = dt.params.zip(sort.args).toMap

    // We want to split the constructors given in the cases from the omitted constructors
    // First, determine all constructors and instantiate them with the type parameters
    val con_sels = (dt.constrs map { case (fun, sels) =>
      (Inst(fun, su), sels map (_.name))
    }).toMap
    val all_cons = con_sels.keySet

    // Generate a map matching cases to the given lhs expressions and tactics
    val con_tactics = cases
      .collect({ case (expr: App, tactic) =>
        (expr.inst, (expr, tactic))
      })
      .toMap

    val given_cons = con_tactics.keySet
    val missing_cons = all_cons &~ given_cons

    // Generate a copy of goal without a top level quantor quantifying the induction `variable`
    val goal_ = goal match {
      case Disj(xs, neg, pos) => Disj(xs.filterNot(_ == variable), neg, pos)
    }

    // Generate goals for every constructor, as Map mapping each constructor to its goal
    all_cons
      .map(inst => {
        val args = if (given_cons contains inst) {
          // HACK! Replace List[Var] somehow.
          val (pattern @ App(_, args: List[Var]), _) = con_tactics(inst)
          assert(args forall (_.isInstanceOf[Var]))
          args
        } else {
          val sels = con_sels(inst)
          Expr.fresh(sels, inst.args)
        }

        val rec_args = args.filter(_.typ == sort)
        val hyps = rec_args map (arg => goal_.subst(Map(variable -> arg)))

        val su = Map(variable -> App(inst, args))

        val new_goal = Disj(
          goal_.xs ++ args,
          goal_.neg.map(_.subst(su)) ++ hyps,
          goal_.pos.map(_.subst(su))
        )

        (new_goal, con_tactics.get(inst) map (_._2))
      })
      .toList
  }
}

case class Show(
    prop: Expr,
    tactic: Option[Tactic],
    cont: Option[Tactic]
) extends Tactic {

  def apply(state: State, goal: Prop) = {
    assert(goal.isInstanceOf[Disj])
    val prop_ = Disj.from(prop)

    val Disj(xs, neg, pos) = goal.asInstanceOf[Disj]
    val goal_ = Disj.assume(List(prop), Nil, xs, neg, pos)

    List(
      (prop_, tactic),
      (goal_, cont)
    )
  }
}

object Unfold
    extends ((Name, Option[List[BigInt]], Option[Tactic]) => Unfold)
    with Suggest {

  // TODO: Consider suggesting unfolding of defined functions?
  def suggest(state: State, goal: Prop): List[Tactic] = Nil

}

case class Unfold(
    target: Name,
    places: Option[List[BigInt]],
    cont: Option[Tactic]
) extends Tactic {
  require(!places.isDefined || places.get.forall(i => 1 <= i))

  def apply(state: State, goal: Prop) = {
    val expr = goal.toExpr

    var i = 0

    val goal_ = expr.topdown {
      case e @ App(inst, args) if inst.fun.name == target =>
        i += 1

        if (places.isDefined && !places.get.contains(i)) {
          e
        } else {
          val arity = args.length
          val (params, body) = state.fundefs((target, arity))

          val su = params.zip(args).toMap

          body.subst(su)
        }

      case e =>
        e
    }

    List((Disj.from(goal_), cont))
  }
}

/** This "tactic" is actually just a wrapper for another tactic. It serves to
  * signal that no automatic proving attempt shall happen, before the contained
  * tactic has been applied.
  *
  * @param tactic
  */
case class NoAuto(tactic: Tactic) extends Tactic {

  def apply(state: State, goal: Prop): List[(Prop, Option[Tactic])] =
    tactic.apply(state, goal)
}

package cuvee.backend

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Name

/** Represents a tactic that can be applied to a proof obligation.
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
  def apply(state: State, goal: Prop): List[(Prop, Option[Tactic])]
}

case object Sorry extends Tactic {
  def apply(state: State, goal: Prop) = {
    // Currently a no-op
    println("\u001b[93m⚠\u001b[0m Use of the \u001b[93msorry\u001b[0m tactic!")
    Nil
  };
}

case class Induction(variable: Var, cases: List[(Expr, Tactic)])
    extends Tactic {
  def apply(state: State, goal: Prop) = {
    // First determine the variable's datatype
    val sort = variable.typ.asInstanceOf[Sort]
    val dt = state.datatypes(sort.con.name)

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
      case _ => cuvee.error("Only Disj supported in induction tactic")
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

case class Show(prop: Expr, tactic: Option[Tactic], cont: Option[Tactic])
    extends Tactic {
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

case class Unfold(target: Name, places: Option[List[BigInt]], cont: Option[Tactic])
    extends Tactic {
  require(!places.isDefined || places.get.forall(i => 1 <= i))

  def apply(state: State, goal: Prop) = {
    val expr = goal.toExpr

    var i = 0

    val goal_ = expr.topdown(e => e match {
      case App(inst, args) if inst.fun.name == target => {
        i += 1

        if (places.isDefined && !places.get.contains(i)) {
          e
        } else {
          val arity = args.length
          val (params, body) = state.fundefs((target, arity))

          val su = params.zip(args).toMap

          body.subst(su)
        }
      }

      case _ => e
    })

    List( (Disj.from(goal_), cont) )
  }
}

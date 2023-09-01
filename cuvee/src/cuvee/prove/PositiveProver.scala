package cuvee.prove

import cuvee.pure._
import cuvee.smtlib.DeclareFun
import cuvee.smtlib._
import cuvee.State

/** This class
  *
  * @param solver
  *   SMT solver to use to check expressions
  */
class PositiveProver(solver: Solver) extends Prover {
  def exec(cmd: Cmd, state: State) {
    solver.exec(cmd, state)
  }

  def reduce(that: Prop, state: State): Prop = that match {
    case Atom(phi: Expr, _) =>
      atom(phi, state)

    case Disj(xs, assms, concls) =>
      disj(xs, assms, concls, state)
  }

  def reduce(that: Conj, state: State): Conj = that match {
    case Conj(Nil, props) =>
      val neg_ = all(props, state)
      Conj.reduce(Nil, neg_)

    case conj: Conj =>
      val prop = atom(conj.toExpr, state)
      Conj.from(prop.toExpr)
  }

  def atom(phi: Expr, state: State): Atom = solver scoped {
    solver.assert(!phi)
    val status = solver.check()

    status match {
      case Sat =>
        Atom(phi, Some(solver.model(state)))
      case Unsat =>
        Atom(True)
      case Unknown =>
        Atom(phi)
    }
  }

  def disj(xs: List[Var], assms: List[Prop], concls: List[Conj], state: State): Prop =
    solver.scoped {
      // A Disj contains variables quantified by a forall quantifier (disj.xs).
      // Below, we'll split those variables from their declaration in the quantifier.
      // Decide how to rename the quantified variables
      val re = Expr.fresh(xs)
      val re_ = re map (_.swap)

      val xs_ = xs rename re
      val assms_ = assms map (_ rename re)
      val concls_ = concls map (_ rename re)

      // Declare the variables from the forall-quantifier
      for (x <- xs_)
        solver.ack(DeclareFun(x.name, Nil, Nil, x.typ))

      for (pre <- assms_)
        solver.assert(pre.toExpr)

      if (concls.isEmpty && solver.isUnsat) {
        // Empty succedent: the only option to close the proof
        // is when the assumptions are already inconsistent.
        // However, do not do this eagerly, because *typically*
        // they are not inconsistent if we have a proper goal.
        Atom.t
      } else {
        // Otherwise: Attempt to prove one formula of the succedent,
        // will succeed anyway if the assumptions are already inconsistent
        val concls__ = any(concls_, state)
        // undo the renaming
        Disj.reduce(xs, assms_ map (_ rename re_), concls__ map (_ rename re_))
      }
    }

  def any(concls: List[Conj], state: State): List[Conj] = concls match {
    case Nil =>
      Nil

    case first :: rest =>
      reduce(first, state) match {
        case Conj(_, Nil) =>
          any(rest, state)

        case first_ =>
          solver.scoped {
            // justification: A \/ B  <==>  (A \/ (!A ==> B))
            solver.assert(!first_.toExpr)
            first_ :: any(rest, state)
          }
      }
  }

  def all(props: List[Prop], state: State): List[Prop] = props match {
    case Nil =>
      Nil

    case first :: rest =>
      reduce(first, state) match {
        case first_ @ Atom(True, _) =>
          all(rest, state)

        case first_ =>
          solver.scoped {
            // justification: A /\ B  <==>  (A /\ (A ==> B))
            solver.assert(first_.toExpr)
            first_ :: all(rest, state)
          }
      }
  }
}

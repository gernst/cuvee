package cuvee.backend

import cuvee.pure._
import cuvee.smtlib.DeclareFun
import cuvee.smtlib._

/** This class
  *
  * @param solver
  *   SMT solver to use to check expressions
  */
class Prove(solver: Solver) {
  def prove(prop: Prop): Prop = prop match {
    case atom: Atom => prove(atom)
    case neg: Neg   => prove(neg)
    case pos: Pos   => prove(pos)
  }

  def prove(atom: Atom): Atom = atom match {
    case Atom(phi, _) =>
      solver scoped {
        solver.assert(!phi)
        val status = solver.check()

        status match {
          case Sat =>
            Atom(phi, Some(solver.model))
          case Unsat =>
            Atom(True)
        }
      }
  }

  def prove(pos: Pos): Pos = pos match {
    case atom: Atom =>
      prove(atom)

    case Conj(Nil, neg) =>
      val neg_ = conj(neg)
      Conj(Nil, neg_)

    case conj: Conj =>
      prove(Atom(conj.toExpr))
  }

  def prove(neg: Neg): Neg = neg match {
    case atom: Atom =>
      prove(atom)

    // forall xs. /\ {ant} ==> \/ {suc}
    case Disj(xs, neg, pos) =>
      solver.scoped {
        // A Disj contains variables quantified by a forall quantifier (disj.xs).
        // Below, we'll split those variables from their declaration in the quantifier.
        // Decide how to rename the quantified variables
        val re = Expr.fresh(xs)
        val re_ = re map (_.swap)

        val xs_ = xs rename re
        val neg_ = neg map (_ rename re)
        val pos_ = pos map (_ rename re)

        // Declare the variables from the forall-quantifier
        for (x <- xs_)
          solver.declare(DeclareFun(x.sexpr, Nil, x.typ))

        for (phi <- neg_)
          solver.assert(phi.toExpr)

        if (pos.isEmpty && solver.isUnsat) {
          // Empty succedent: the only option to close the proof
          // is when the assumptions are already inconsistent.
          // However, do not do this eagerly, because *typically*
          // they are not inconsistent if we have a proper goal.
          Atom(True)
        } else {
          // Otherwise: Attempt to prove one formula of the succedent,
          // will succeed anyway if the assumptions are already inconsistent
          val pos__ = disj(pos_)
          // undo the renaming
          Disj(xs, neg_ map (_ rename re_), pos__ map (_ rename re_))
        }
      }
  }

  def disj(suc: List[Pos]): List[Pos] = suc match {
    case Nil =>
      Nil

    case first :: rest =>
      prove(first) match {
        case first_ @ Atom(False, _) =>
          disj(rest)

        case first_ =>
          solver.scoped {
            // justification: A \/ B  <==>  (A \/ (!A ==> B))
            solver.assert(!first_.toExpr)
            first_ :: disj(rest)
          }
      }
  }

  def conj(ant: List[Neg]): List[Neg] = ant match {
    case Nil =>
      Nil

    case first :: rest =>
      prove(first) match {
        case first_ @ Atom(True, _) =>
          conj(rest)

        case first_ =>
          // TODO: check if we need to scope this
          solver.scoped {
            // justification: A /\ B  <==>  (A /\ (A ==> B))
            solver.assert(first_.toExpr)
            first_ :: conj(rest)
          }
      }
  }
}

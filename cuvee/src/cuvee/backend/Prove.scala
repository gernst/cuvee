package cuvee.backend

import cuvee.pure._
import cuvee.smtlib.DeclareFun

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
    case Atom(phi) =>
      println("ask solver if " + phi + " is true")
      if (solver.isTrue(phi))
        Atom(True)
      else
        atom
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
        //
        val xs_ = xs rename re
        val neg_ = neg map (_ rename re)
        val pos_ = pos map (_ rename re)

        // Declare the variables from the forall-quantifier
        for (x <- xs_)
          solver.declare(DeclareFun(x.sexpr, Nil, x.typ))

        // Attempt to prove the antecedent
        // println("try proving " + ant)
        // val ant_ = prove(ant)

        for (phi <- neg_)
          solver.assert(phi.toExpr)

        if (solver.isUnsat) {
          Atom(True)
        } else {
          // Attempt to disprove the succedent
          val pos__ = disj(pos_)
          Disj(xs_, neg_, pos__)
        }
      }
  }

  def disj(suc: List[Pos]): List[Pos] = suc match {
    case Nil =>
      Nil

    case first :: rest =>
      prove(first) match {
        case first_ @ Atom(False) =>
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
        case first_ @ Atom(True) =>
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

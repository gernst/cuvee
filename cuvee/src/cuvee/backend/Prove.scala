package cuvee.pure

import cuvee.backend.Solver
import cuvee.smtlib.DeclareFun

/**
  * This class
  *
  * @param solver SMT solver to use to check expressions
  */
class Prove(solver: Solver) {

  def disprove(pos: Pos): Pos = pos match {
    case Atom(phi) =>
      if (solver.isFalse(phi))
        Atom(False)
      else
        pos

    case Conj(Nil, ant, suc) =>
      solver.scoped {
        val ant_ = prove(ant)

        // A /\ !B  <==>  (A /\ (A ==> !B))
        for (phi <- ant_)
          solver.assert(phi.toExpr)

        val suc_ = disprove(suc)
        Conj(Nil, ant_, suc_)
      }

    // maybe eliminate
    // exists x. x == e /\ P(x)
    // ~>  P(e)
    case conj: Conj =>
      val phi = conj.toExpr
      if (solver.isFalse(phi))
        Atom(False)
      else
        conj
  }

  def prove(neg: Neg): Neg = neg match {
    case Atom(phi) =>
      if (solver.isTrue(phi))
        Atom(True)
      else
        neg

    case disj: Disj =>
      solver.scoped {
        // A Disj contains variables quantified by a forall quantifier (disj.xs).
        // Below, we'll split those variables from their declaration in the quantifier.
        // Decide how to rename the quantified variables
        val xs_ = Expr.fresh(disj.xs)
        // 
        val xs__ = xs_.values.toList
        val ant = disj.neg map (_.rename(xs_))
        val suc = disj.pos map (_.rename(xs_))

        // Declare the variables from the forall-quantifier
        for (x <- xs__)
          solver.declare(DeclareFun(x.sexpr, Nil, x.typ))

        // Attempt to prove the antecedent
        val ant_ = prove(ant)

        for (phi <- ant_)
          solver.assert(phi.toExpr)

        // Attempt to disprove the succedent
        val suc_ = disprove(suc)
        Disj(xs__, ant_, suc_)
      }
  }

  def disprove(suc: List[Pos]): List[Pos] = suc match {
    case Nil =>
      Nil

    case first :: rest =>
      disprove(first) match {

        case first_ @ Atom(False) =>
          disprove(rest)

        case first_ =>
          // TODO: check if we need to scope this
          solver.scoped {
            // justification: A \/ B  <==>  (A \/ (!A ==> B))
            solver.assert(!first_.toExpr)
            first_ :: disprove(rest)
          }
      }
  }

  def prove(ant: List[Neg]): List[Neg] = ant match {
    case Nil =>
      Nil

    case first :: rest =>
      prove(first) match {
        case first_ @ Atom(True) =>
          prove(rest)

        case first_ =>
          // TODO: check if we need to scope this
          solver.scoped {
            // justification: A /\ B  <==>  (A /\ (A ==> B))
            solver.assert(!first_.toExpr)
            first_ :: prove(rest)
          }
      }
  }
}
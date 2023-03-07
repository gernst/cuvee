package cuvee.backend

import cuvee.pure._
import cuvee.smtlib.DeclareFun

class BimodalProver(solver: Solver) extends Prover {
  def prove(prop: Prop): Prop = prove(prop, true);

  def prove(prop: Prop, expect: Boolean): Prop = prop match {
    case atom: Atom => prove(atom, expect)
    case neg: Neg   => prove(neg, expect)
    case pos: Pos   => prove(pos, expect)
  }

  def prove(atom: Atom, expect: Boolean): Atom = {
    // println("trying: " + atom.expr + " == " + expect)

    atom match {
      case Atom(phi, _) if expect && solver.isTrue(phi) =>
        Atom.t

      case Atom(phi, _) if !expect && solver.isFalse(phi) =>
        Atom.f

      case _ =>
        atom
    }
  }

  def prove(pos: Pos, expect: Boolean): Pos = pos match {
    case atom: Atom =>
      prove(atom, expect)

    case Conj(Nil, neg) =>
      val neg_ = conj(neg, expect)

      neg_ match {
        case Nil =>
          Atom.t
        case neg_ if neg_ contains Atom.f =>
          Atom.f
        case _ =>
          Conj(Nil, neg_)
      }

    case Conj(xs, neg) =>
      val re = Expr.fresh(xs)
      val re_ = re map (_.swap)

      val xs_ = xs rename re
      val neg_ = neg map (_ rename re)

      val neg__ = conj(neg_, expect)

      val res = neg__ match {
        case Nil =>
          Atom.t
        case _ if neg__ contains Atom.f =>
          Atom.f
        case _ =>
          Conj(xs, neg__ map (_ rename re_))
      }

      if (xs.nonEmpty && expect && solver.isTrue(res.toExpr)) {
        Atom.t
      } else {
        res
      }
  }

  def prove(neg: Neg, expect: Boolean): Neg = neg match {
    case atom: Atom =>
      prove(atom, expect)

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

        // Filter out redundant assumptions, always expect true
        val neg__ = neg_ // conj(neg_, expect)

        // Add assumptions to the solver
        for (phi <- neg__)
          solver.assert(phi.toExpr)

        // Filter out redundant conclusions
        val pos__ = disj(pos_, expect)

        val res = pos__ match {
          case Nil =>
            Atom.f
          case _ if pos__ contains Atom.t =>
            Atom.t
          case _ =>
            // Undo the substitution
            Disj(xs, neg__ map (_ rename re_), pos__ map (_ rename re_))
        }

        if (xs.nonEmpty && !expect && solver.isFalse(res.toExpr)) {
          Atom.f
        } else {
          res
        }
      }
  }

  def disj(suc: List[Pos], expect: Boolean): List[Pos] = suc match {
    case Nil if expect && solver.isUnsat =>
      List(Atom.t)

    case Nil =>
      Nil

    case first :: rest =>
      prove(first, expect = false) match {
        case Atom.f =>
          disj(rest, expect)

        case first_ =>
          solver.scoped {
            solver.assert(!first_.toExpr)
            first :: disj(rest, expect)
          }
      }
  }

  def conj(ant: List[Neg], expect: Boolean): List[Neg] = ant match {
    case Nil if !expect && solver.isUnsat =>
      List(Atom.f)

    case Nil =>
      Nil

    case first :: rest =>
      prove(first, expect = true) match {
        case Atom.t =>
          conj(rest, expect)

        case first_ =>
          solver.scoped {
            solver.assert(first_.toExpr)
            first :: conj(rest, expect)
          }
      }
  }
}

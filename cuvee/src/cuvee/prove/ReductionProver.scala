package cuvee.prove

import cuvee.pure._
import cuvee.smtlib._
import cuvee.State

class ReductionProver(solver: Solver) extends Prover {
    def exec(cmd: Cmd, state: State) {
      solver.exec(cmd, state)
    }
  
  def reduce(prop: Prop, state: State): Prop = reduce(prop, true, state);

  def reduce(prop: Prop, expect: Boolean, state: State): Prop = prop match {
    case atom: Atom => reduce(atom, expect, state)
    case neg: Neg   => reduce(neg, expect, state)
    case pos: Pos   => reduce(pos, expect, state)
  }

  def reduce(atom: Atom, expect: Boolean, state: State): Atom = {
    atom match {
      // Shortcut, if formula is already true / false
      case Atom.t if expect => Atom.t
      case Atom.f if !expect => Atom.f

      // Try to prove the atom
      case Atom(phi, _) if expect =>
        solver.scoped {
          solver.assert(!phi)

          solver.check() match {
            case Sat =>
              Atom(phi, Some(solver.model(state)))
            case Unsat => Atom.t
            case Unknown => atom
          }
        }

      // Try to disprove the atom
      case Atom(phi, _) if !expect =>
        solver.scoped {
          solver.assert(phi)

          solver.check() match {
            case Sat =>
              Atom(phi, Some(solver.model(state)))
            case Unsat => Atom.f
            case Unknown => atom
          }
        }
    }
  }

  def reduce(pos: Pos, expect: Boolean): Pos = pos match {
    case atom: Atom =>
      reduce(atom, expect)

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
      solver.scoped {
        // A Conj contains variables quantified by a exists quantifier (conj.xs).
        // Below, we'll split those variables from their declaration in the quantifier.

        // Substitute the bound variables with *fresh* variables
        val re = Expr.fresh(xs)
        val re_ = re map (_.swap)

        val xs_ = xs rename re
        val neg_ = neg map (_ rename re)

        // Declare the variables from the exists-quantifier
        for (x <- xs_)
          solver.ack(DeclareFun(x.sexpr, Nil, Nil, x.typ))

        // Filter out redundant elements
        val neg__ = conj(neg_, expect)

        val res = neg__ match {
          case Nil =>
            Atom.t
          case _ if neg__ contains Atom.f =>
            Atom.f
          case _ =>
            // Undo the substitution
            Conj(xs, neg__ map (_ rename re_))
        }

        // Return the result
        if (xs.nonEmpty && expect && solver.isTrue(res.toExpr)) {
          Atom.t
        } else {
          res
        }
      }
  }

  def reduce(neg: Neg, expect: Boolean): Neg = neg match {
    case atom: Atom =>
      reduce(atom, expect)

    case Disj(xs, neg, pos) =>
      solver.scoped {
        // A Disj contains variables quantified by a forall quantifier (disj.xs).
        // Below, we'll split those variables from their declaration in the quantifier.

        // Substitute the bound variables with *fresh* variables
        val re = Expr.fresh(xs)
        val re_ = re map (_.swap)

        val xs_ = xs rename re
        val neg_ = neg map (_ rename re)
        val pos_ = pos map (_ rename re)

        // Declare the variables from the forall-quantifier
        for (x <- xs_)
          solver.ack(DeclareFun(x.sexpr, Nil, Nil, x.typ))

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

        // Return the result
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
      reduce(first, expect = false) match {
        case Atom.f =>
          disj(rest, expect)

        case first_ =>
          solver.scoped {
            solver.assert(!first_.toExpr)
            first_ :: disj(rest, expect)
          }
      }
  }

  def conj(ant: List[Neg], expect: Boolean): List[Neg] = ant match {
    case Nil if !expect && solver.isUnsat =>
      List(Atom.f)

    case Nil =>
      Nil

    case first :: rest =>
      reduce(first, expect = true) match {
        case Atom.t =>
          conj(rest, expect)

        case first_ =>
          solver.scoped {
            solver.assert(first_.toExpr)
            first_ :: conj(rest, expect)
          }
      }
  }
}

package cuvee.pure

import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib._

object Clause extends Stage {
  override def exec(
      prefix: List[Cmd],
      cmds: List[Cmd],
      last: Cmd,
      in: State
  ): List[Cmd] = {
    cmds map {
      case Lemma(expr, tactic, flag, named) =>
        val expr_ = sequent(expr.free, expr)
        Lemma(expr_, tactic, flag, named)

      case cmd =>
        cmd
    }
  }

  def apply(xs: List[Var], ant: List[Expr], suc: Expr) =
    (xs, ant) match {
      case (Nil, Nil) => suc
      case (Nil, _)   => Imp(And(ant), suc)
      case (_, Nil)   => Forall(xs, suc)
      case _          => Forall(xs, Imp(And(ant), suc))
    }

  def apply(xs: List[Var], ant: Expr, suc: Expr) =
    (xs, ant) match {
      case (Nil, True) => suc
      case (Nil, _)    => Imp(ant, suc)
      case (_, True)   => Forall(xs, suc)
      case _           => Forall(xs, Imp(ant, suc))
    }

  def unapply(expr: Expr) =
    expr match {
      case Forall(xs, Imp(And(ant), suc)) => Some((xs, ant, suc))
      case Forall(xs, Imp(ant, suc))      => Some((xs, List(ant), suc))
      case Forall(xs, suc)                => Some((xs, Nil, suc))
      case Imp(And(ant), suc)             => Some((Nil, ant, suc))
      case Imp(ant, suc)                  => Some((Nil, List(ant), suc))
      case _                              => Some((Nil, Nil, expr))
    }

  def nnf(phi: Expr): Expr = phi match {
    case Not(App(Fun.and, List(phi, psi))) =>
      Or(Simplify.not(nnf(phi)), Simplify.not(nnf(psi)))

    case Not(App(Fun.or, List(phi, psi))) =>
      And(Simplify.not(nnf(phi)), Simplify.not(nnf(psi)))

    case Not(Not(phi)) =>
      nnf(phi)

    case _ =>
      phi
  }

  def dnf(phi: Expr): List[List[Expr]] = phi match {
    case App(Fun.or, List(phi, psi)) =>
      dnf(phi) ++ dnf(psi)

    case App(Fun.and, List(phi, psi)) =>
      for (a <- dnf(phi); b <- dnf(psi))
        yield a ++ b

    case _ =>
      List(List(phi))
  }

  def isSimpleSequent(prop: Expr) = {
    prop match {
      case phi if phi.isAtomic      => true
      case Not(phi) if phi.isAtomic => true
      case _                        => false
    }
  }

  def isSimpleGoal(prop: Expr) = {
    prop match {
      case phi if phi.isAtomic => true
      case _                   => false
    }
  }

  def flatten(bound: Set[Var], prop: Expr): Option[(List[Var], List[Expr], List[Expr])] = {
    flatten(bound, Nil, List(prop))
  }

  def sequent(bound: Set[Var], prop: Expr): Expr = {
    if (isSimpleSequent(prop)) {
      prop
    } else {
      flatten(bound, Nil, List(prop)) match {
        case None =>
          True

        case Some((xs, ant, suc)) =>
          Clause(xs, ant, Or(suc))
      }
    }
  }

  def goal(bound: Set[Var], prop: Expr): Expr = {
    if (isSimpleGoal(prop)) {
      prop
    } else {
      flatten(bound, List(prop), Nil) match {
        case None =>
          False

        case Some((Nil, ant, suc)) =>
          And(ant ++ Not(suc))

        case Some((xs, ant, suc)) =>
          Exists(xs, And(ant ++ Not(suc)))
      }
    }
  }

  def flatten(
      bound: Set[Var],
      pos: List[Expr],
      neg: List[Expr]
  ): Option[(List[Var], List[Expr], List[Expr])] = {
    (pos, neg) match {
      case (Nil, Nil)          => Some((Nil, Nil, Nil))
      case (False :: pos, neg) => None // trivial
      case (pos, True :: neg)  => None // trivial

      case (True :: pos, neg)      => flatten(bound, pos, neg)
      case (And(phis) :: pos, neg) => flatten(bound, phis ++ pos, neg)

      case (pos, False :: neg)         => flatten(bound, pos, neg)
      case (pos, Imp(phi, psi) :: neg) => flatten(bound, phi :: pos, psi :: neg)
      case (pos, Or(phis) :: neg)      => flatten(bound, pos, phis ++ neg)

      case (Not(phi) :: pos, neg) if !phi.isAtomic =>
        // otherwise: keep all negated atomic formulas in the consequent
        flatten(bound, pos, phi :: neg)

      case (pos, Not(phi) :: neg) =>
        flatten(bound, phi :: pos, neg)

      case ((bind @ Exists(_, _)) :: pos, neg) =>
        val Exists(xs, phi) = bind refresh bound
        for ((ys, ant, suc) <- flatten(bound ++ xs, phi :: pos, neg))
          yield (xs ++ ys, ant, suc)

      case (pos, (bind @ Forall(_, _)) :: neg) =>
        val Forall(xs, phi) = bind refresh bound
        for ((ys, ant, suc) <- flatten(bound ++ xs, pos, phi :: neg))
          yield (xs ++ ys, ant, suc)

      // NOTE: the ones below possibly interfere with simplify and generally blow up the formula
      //       but consider re-adding these, and instantiate other conjuncts/disjuncts when building up contexts?

      // case (pos, Exists(ys, Or(phis)) :: neg) =>
      //   val phis_ = phis map (Exists(ys, _))
      //   flatten(bound, pos, phis_ ++ neg)

      // case (Forall(ys, And(phis)) :: pos, neg) =>
      //   val phis_ = phis map (Forall(ys, _))
      //   flatten(bound, phis_ ++ pos, neg)

      // case (pos, Exists(ys, Ite(test, left, right)) :: neg) =>
      //   val phi = Exists(ys, test && left)
      //   val psi = Exists(ys, !test && right)
      //   flatten(bound, pos, phi :: psi :: neg)

      // case (Forall(ys, Ite(test, left, right)) :: pos, neg) =>
      //   val phi = Forall(ys, Imp(test, left))
      //   val psi = Forall(ys, Imp(!test, right))
      //   flatten(bound, phi :: psi :: pos, neg)

      case (Let(eqs, body) :: pos, neg) =>
        val phi = Exists(eqs.vars, And(eqs.toEqs ++ List(body)))
        flatten(bound, phi :: pos, neg)

      case (pos, Let(eqs, body) :: neg) =>
        val phi = Forall(eqs.vars, And(eqs.toEqs) ==> body)
        flatten(bound, pos, phi :: neg)

      case (phi :: pos, neg) =>
        sequent(bound, phi) match {
          case `phi` => // continue to flatten other formulas
            for ((ys, ant, suc) <- flatten(bound, pos, neg))
              yield (ys, phi :: ant, suc)

          case phi_ => // try another round
            flatten(bound, phi_ :: pos, neg)
        }

      case (pos, phi :: neg) =>
        goal(bound, phi) match {
          case `phi` => // continue to flatten other formulas
            for ((ys, ant, suc) <- flatten(bound, pos, neg))
              yield (ys, ant, phi :: suc)

          case phi_ => // try another round
            flatten(bound, pos, phi_ :: neg)
        }
    }
  }
}

package cuvee.ai

import cuvee.pure._
import cuvee.util.Name
import cuvee.imp.Spec

trait Domain[S] {
  def top: S
  def subsetOf(s1: S, s2: S): Boolean

  def free(s: S): Set[Var]
  def constraints(s: S): List[Expr]

  // update states with additional information
  def assume(s: S, phi: Expr): List[(S, List[Expr])]
  def rename(s: S, re: Map[Var, Var]): S
  def subst(s: S, su: Map[Var, Expr]): List[S] // narrow to this instance, possibly bottom

  def entry(in: List[Var], out: List[Var], spec: Option[Spec]): List[S]

  // Note:
  def step(s: S, xs: List[Var], rel: Expr): List[S]
  def local(s: S, xs: List[Var], rhs: List[Expr]): List[S]
  def assign(s: S, xs: List[Var], rhs: List[Expr]): List[S]

  // lattice operations on entire states
  def join(s1: S, sn2: List[S]): List[S]
  def meet(s1: S, sn2: List[S]): List[S]
  def widen(s1: S, sn2: List[S]): List[S]
  def narrow(s1: S, sn2: List[S]): List[S]

  def join(sn: List[S]): List[S] =
    sn match {
      case Nil       => Nil
      case s1 :: sn2 => join(s1, sn2)
    }

  def meet(sn: List[S]): List[S] =
    sn match {
      case Nil       => List(top) // strange!
      case s1 :: sn2 => meet(s1, sn2)
    }
}

object Domain {
  object NotNumeric extends Exception

  trait Numeric[E, S] {
    def literal(value: BigInt): E
    def variable(name: Name): E

    def plus(exprs: List[E]): E
    def times(exprs: List[E]): E
    def minus(left: E, right: E): E
    def divBy(left: E, right: E): E

    def neq(s: S, left: E, right: E): S
    def eq(s: S, left: E, right: E): S
    def le(s: S, left: E, right: E): S
    def lt(s: S, left: E, right: E): S

    def term(expr: Expr): E = expr match {
      case Lit(value: BigInt, Sort.int) =>
        literal(value)

      case Var(name, typ) =>
        variable(name)

      case Plus(exprs) =>
        plus(exprs map term)

      case Times(exprs) =>
        times(exprs map term)

      case Minus(left, right) =>
        minus(term(left), term(right))

      case DivBy(left, right) =>
        divBy(term(left), term(right))

      case _ =>
        throw NotNumeric
    }

    def tryNumeric(s: S, e: Expr)(f: => S) = {
      try {
        (List(f -> Nil))
      } catch {
        case NotNumeric =>
          List(s -> List(e))
      }
    }

    def constraints(s: S, expr: Expr): List[(S, List[Expr])] = expr match {
      case And(args) =>
        val cs0 = List(s -> (Nil: List[Expr]))

        args.foldRight(cs0) { case (arg, cs) =>
          for (
            (s, es) <- cs;
            (s_, e) <- constraints(s, arg)
          )
            yield (s_, e ++ es)
        }

      case Not(arg) =>
        arg match {
          case Eq(left, right) =>
            tryNumeric(s, expr) { neq(s, term(left), term(right)) }

          case Le(left, right) =>
            tryNumeric(s, expr) { lt(s, term(right), term(left)) }

          case Lt(left, right) =>
            tryNumeric(s, expr) { le(s, term(right), term(left)) }

          case Ge(left, right) =>
            tryNumeric(s, expr) { lt(s, term(left), term(right)) }

          case Gt(left, right) =>
            tryNumeric(s, expr) { le(s, term(left), term(right)) }

          case And(args) =>
            // De Morgan:  Not(And(a, b)) transforms to Or(Not(a), Not(b))
            constraints(s, Or(Not(args)))

          case Imp(phi, psi) =>
            // Not(phi → psi) transforms to phi ∧ Not(psi)
            constraints(s, And(phi, Not(psi)))

          case Not(arg) =>
            constraints(s, arg) // Not(Not(arg)) == arg

          case _ =>
            List(s -> List(expr)) // we don't know
        }

      case Imp(phi, psi) =>
        constraints(s, Or(List(Not(phi), psi)))

      case Eq(left, right) if left.typ == Sort.int =>
        tryNumeric(s, expr) { eq(s, term(left), term(right)) }

      case Le(left, right) =>
        tryNumeric(s, expr) { le(s, term(left), term(right)) }

      case Lt(left, right) =>
        tryNumeric(s, expr) { lt(s, term(left), term(right)) }

      case Ge(left, right) =>
        tryNumeric(s, expr) { le(s, term(right), term(left)) }

      case Gt(left, right) =>
        tryNumeric(s, expr) { lt(s, term(right), term(left)) }

      case _ =>
        List((s -> List(expr))) // we don't know
    }
  }
}

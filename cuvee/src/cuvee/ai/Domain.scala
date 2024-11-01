package cuvee.ai

import cuvee.pure._
import cuvee.util.Name
import cuvee.imp.Spec

trait DomainFunctions {
  // let s1 with xs == args1 and phis1
  // let s2 with xs == args2 and phis2
  // compute widen(s1, s2) and eliminate xs
  // satisfying s1 \/ s2 ==> result and guarantee finite convergence
  def widen(
      args1: List[Expr],
      phis1: List[Expr],
      args2: List[Expr],
      phis2: List[Expr]
  ): List[Expr] = {
    ???
  }
}


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
  def join(first: S, rest: List[S]): List[S]
  def meet(first: S, rest: List[S]): List[S]
  def widen(prev: S, next: List[S]): List[S]
  def narrow(prev: S, next: List[S]): List[S]

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
    def arbitrary: E

    def literal(s: S, value: BigInt): E
    def variable(s: S, x: Var): E

    def plus(s: S, exprs: List[E]): E
    def times(s: S, exprs: List[E]): E
    def minus(s: S, left: E, right: E): E
    def divBy(s: S, left: E, right: E): E

    def neq(s: S, left: E, right: E): S
    def eq(s: S, left: E, right: E): S
    def le(s: S, left: E, right: E): S
    def lt(s: S, left: E, right: E): S

    def eval(s: S, exprs: List[Expr]): List[E] =
      exprs map { eval(s, _) }

    def eval(s: S, expr: Expr): E = expr match {
      case Lit(value: BigInt, Sort.int) =>
        literal(s, value)

      case x: Var =>
        variable(s, x)

      case Plus(args) =>
        plus(s, eval(s, args))

      case Times(args) =>
        times(s, eval(s, args))

      case Minus(arg1, arg2) =>
        minus(s, eval(s, arg1), eval(s, arg2))

      case DivBy(arg1, arg2) =>
        divBy(s, eval(s, arg1), eval(s, arg2))

      case _ =>
        arbitrary
    }

    def yes(s: S) =
      List(s -> Nil)

    def no(s: S, e: Expr) =
      List(s -> List(e))

    def assume(s: S, expr: Expr): List[(S, List[Expr])] = expr match {
      case And(args) =>
        val cs0 = List(s -> (Nil: List[Expr]))

        args.foldRight(cs0) { case (arg, cs) =>
          for (
            (s, es) <- cs;
            (s_, e) <- assume(s, arg)
          )
            yield (s_, e ++ es)
        }

      case Not(arg) =>
        arg match {
          case Eq(left, right) =>
            yes { neq(s, eval(s, left), eval(s, right)) }

          case Le(left, right) =>
            yes { lt(s, eval(s, right), eval(s, left)) }

          case Lt(left, right) =>
            yes { le(s, eval(s, right), eval(s, left)) }

          case Ge(left, right) =>
            yes { lt(s, eval(s, left), eval(s, right)) }

          case Gt(left, right) =>
            yes { le(s, eval(s, left), eval(s, right)) }

          case And(args) =>
            // De Morgan:  Not(And(a, b)) transforms to Or(Not(a), Not(b))
            assume(s, Or(Not(args)))

          case Imp(phi, psi) =>
            // Not(phi → psi) transforms to phi ∧ Not(psi)
            assume(s, And(phi, Not(psi)))

          case Not(arg) =>
            assume(s, arg) // Not(Not(arg)) == arg

          case _ =>
            no(s, expr) // we don't know
        }

      case Imp(phi, psi) =>
        assume(s, Or(List(Not(phi), psi)))

      case Eq(left, right) if left.typ == Sort.int =>
        yes { eq(s, eval(s, left), eval(s, right)) }

      case Le(left, right) =>
        yes { le(s, eval(s, left), eval(s, right)) }

      case Lt(left, right) =>
        yes { lt(s, eval(s, left), eval(s, right)) }

      case Ge(left, right) =>
        yes { le(s, eval(s, right), eval(s, left)) }

      case Gt(left, right) =>
        yes { lt(s, eval(s, right), eval(s, left)) }

      case _ =>
        no(s, expr) // we don't know
    }
  }
}

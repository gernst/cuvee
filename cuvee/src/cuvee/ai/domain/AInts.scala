package cuvee.ai.domain

import cuvee.ai.Domain
import cuvee.ai.AInt
import cuvee.pure._
import cuvee.imp.Spec
import cuvee.ai.NegInf
import cuvee.ai.PosInf
import cuvee.ai.Fin
import cuvee.util.Name

case class AState(vars: Map[Var, AInt]) {
  def map(f: ((Var, AInt)) => (Var, AInt)) =
    AState(vars map f)
}

object AState {
  val empty = AState(Map())
}

object AInts extends Domain[AState] with Domain.Numeric[AInt, AState] {
  def arbitrary =
    AInt.top

  def top =
    AState.empty

  def literal(s: AState, value: BigInt) =
    AInt(value)

  def variable(s: AState, x: Var) =
    s vars x

  def plus(s: AState, exprs: List[AInt]) =
    exprs reduce (_ + _)

  def times(s: AState, exprs: List[AInt]) =
    exprs reduce (_ * _)

  def minus(s: AState, left: AInt, right: AInt) =
    left - right

  def divBy(s: AState, left: AInt, right: AInt) =
    left / right

  def eq(s: AState, left: AInt, right: AInt): AState = ???

  def neq(s: AState, left: AInt, right: AInt): AState = ???

  def le(s: AState, left: AInt, right: AInt): AState = ???

  def lt(s: AState, left: AInt, right: AInt): AState = ???

  def free(s: AState) =
    s.vars.keySet

  def subsetOf(s1: AState, s2: AState) = {
    s1.vars forall {
      case (x, v1) if s2.vars contains x =>
        val v2 = s2 vars x
        v2.lb <= v1.lb && v1.ub <= v2.ub

      case _ =>
        // s2 does not constrain x
        true
    }
  }

  def constraints(x: Var, v: AInt) = v match {
    case AInt(NegInf, PosInf) =>
      List()
    case AInt(NegInf, Fin(ub)) =>
      List(x <= Lit(ub, Sort.int))
    case AInt(Fin(lb), PosInf) =>
      List(Lit(lb, Sort.int) <= x)
    case AInt(Fin(lb), Fin(ub)) =>
      List(Lit(lb, Sort.int) <= x, x <= Lit(ub, Sort.int))
  }

  def constraints(s: AState) = {
    for (
      (x, v) <- s.vars.toList;
      phi <- constraints(x, v)
    )
      yield phi
  }

  def rename(s: AState, re: Map[Var, Var]) =
    s map { case (x, v) => (x rename re, v) }

  def subst(s: AState, su: Map[Var, Expr]) =
    List(s map { case (x, v) => (x, eval(s, su(x))) })

  def entry(in: List[Var], out: List[Var], spec: Option[Spec]) = {
    spec match {
      case None =>
        val vars = in ++ out map { _ -> arbitrary }
        val as = AState(Map(vars: _*))
        List(as)

      case Some(Spec(globals, pre, post)) =>
        val vars = in ++ out ++ globals map { _ -> arbitrary }
        val as = AState(Map(vars: _*))
        val as_ = assume(as, pre) map { _._1 }
        as_
    }
  }

  def step(s: AState, xs: List[Var], rel: Expr) = {
    ???
  }

  def local(s: AState, xs: List[Var], rhs: List[Expr]): List[AState] = {
    ???
  }

  def assign(s: AState, xs: List[Var], rhs: List[Expr]) = {
    val AState(vars) = s
    val values = eval(s, rhs)
    val s_ = AState(vars ++ (xs zip values))
    List(s_)
  }

  def join(first: AState, rest: List[AState]): List[AState] = ???
  def meet(first: AState, rest: List[AState]): List[AState] = ???
  def widen(prev: AState, next: List[AState]): List[AState] = ???
  def narrow(prev: AState, next: List[AState]): List[AState] = ???
}

package cuvee.backend

import cuvee.pure._
import cuvee.smtlib.Cmd

/**
  * Represents a tactic that can be applied to a proof obligation.
  */
trait Tactic {
  def apply(prop: Prop): List[(Prop, Option[Tactic])]
}

case object Sorry extends Tactic {
  def apply(prop: Prop) = {
    println(">> sorry >>  " + prop.toExpr)

    Nil
  };
}

case class Induction(variable: Var, cases: List[(Expr, Tactic)]) extends Tactic {
  def apply(prop: Prop) = {
    // Currently, this is only implemented for integers
    assert(variable.typ == Sort.int)
    // At the moment, this assumes that there are *exactly* two cases and that the first case is the zero case, the second one the succ(x) case.
    assert(cases.length == 2)

    val prop_ = prop match {
      case Conj(xs, neg, pos) => Conj(xs.filterNot(_ == variable), neg, pos)
      case Disj(xs, neg, pos) => Disj(xs.filterNot(_ == variable), neg, pos)
      case _ => prop
    }

    val Disj(xs, pos, neg) = Disj.show(List(prop_.toExpr), Nil, Nil, Nil)

    // Build a formula that states the induction hypothesis, i.e. forall m : int :: m < variable ==> P(m)
    // TODO: Actually choose a new name, not just "m" → use prop
    val n = variable
    val m = variable.prime

    val lt = App(Inst(Fun("<", Nil, List(Sort.int, Sort.int), Sort.bool), Map()), List(m, n))
    val ind = Bind(Quant("forall"), List(m), Imp(lt, prop_.subst(Map(variable -> m)).toExpr), Sort.bool)

    // TODO: Once constructors / datatypes are available, generate a list of all constructors and handle undefined cases automatically

    List(
      (prop_.subst(Map(variable -> Lit(0, Sort.int))), Some(cases(0)._2)),
      (Disj.assume(List(ind), Nil, xs, pos, neg), Some(cases(1)._2))
    )
  };
}
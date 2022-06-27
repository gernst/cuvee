package cuvee.backend

import cuvee.pure.Prop
import cuvee.pure.Expr
import cuvee.smtlib.Cmd
import cuvee.pure.Var
import cuvee.pure.Sort

/**
  * Represents a tactic that can be applied to a proof obligation.
  */
trait Tactic {
  def apply(prop: Prop): List[(Prop, Option[Tactic])]
}

object Sorry extends Tactic {
  def apply(prop: Prop) = {
    println("=================  GOAL  =================")
    println(prop.toExpr)

    Nil
  };
}

case class Induction(variable: Var, cases: List[(Expr, Tactic)]) extends Tactic {
  def apply(prop: Prop) = {
    // Currently, this is only implemented for integers
    assert(variable.typ == Sort.int)
    // At the moment, this assumes that there are *exactly* two cases and that the first case is the zero case, the second one the succ(x) case.
    assert(cases.length == 2)

    println(s"Using the induction tactic on variable'${variable.name}'")

    List(

    )
  };
}
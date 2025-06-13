package cuvee.imp.traces

import cuvee.pure._

case class Invariant(
    iteration: Iteration,
    result: Expr
) extends Extra
    with Expr.bind2[Invariant] {
  require(result.typ == Sort.bool, "invariant not of type bool, found: " + result.toStringTyped)

  def typ = Sort.bool
  def bound = iteration.bound
  def funs = iteration.funs ++ result.funs
  def free = iteration.free ++ (result.free -- bound)

  def inst(su: Map[Param, Type]) =
    Invariant(
      iteration inst su,
      result inst su
    )

  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr =
    ???

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Invariant(
      iteration rename (a, are),
      result rename are
    )

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Invariant(
      iteration subst (a, asu),
      result subst asu
    )

  override def toString = {
    import cuvee.StringOps
    "invariant(for " + iteration + " assert " + result + ")"
  }
}

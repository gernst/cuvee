package cuvee.imp.traces

import cuvee.pure._

case class Mapping(
    iteration: Iteration,
    result: Expr
) extends Extra
    with Expr.bind2[Mapping] {
  def typ = Sort.trace(result.typ)
  def bound = iteration.bound
  def funs = iteration.funs ++ result.funs
  def free = iteration.free ++ (result.free -- bound)

  def inst(su: Map[Param, Type]) =
    Mapping(
      iteration inst su,
      result inst su
    )

  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr =
    ???

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Mapping(
      iteration rename (a, are),
      result rename are
    )

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Mapping(
      iteration subst (a, asu),
      result subst asu
    )

  override def toString = {
    import cuvee.StringOps
    "map(for " + iteration + " yield " + result + ")"
  }
}

package cuvee.imp.traces

import cuvee.pure._

case class Invariant(
    formals: List[LetEq],
    result: Expr
) extends Extra
    with Expr.bind2[Invariant] {
  // require(result.typ == Sort.bool, "not boolean: " + result.toStringTyped)
  // cannot be checked on unresolved instances

  def typ = Sort.bool
  def bound = Set(formals.vars: _*)
  def funs = formals.funs ++ result.funs
  def free = formals.free ++ (result.free -- bound)

  def gen = {
    // rename all bound variables
    val re = Expr.fresh(bound)
    rename(re, re, re)
  }
  
  def inst(su: Map[Param, Type]) =
    Invariant(
      formals inst su,
      result inst su
    )

  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr =
    ???

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Invariant(
      formals rename (a, are),
      result rename are
    )

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Invariant(
      formals subst (a, asu),
      result subst asu
    )

  override def toString = {
    val iteration =
      if (formals.isEmpty) ""
      else "for " + formals.vars.mkString(", ") + " <- " + formals.args.mkString(", ")

    "invariant(" + iteration + " yield " + result + ")"
  }
}

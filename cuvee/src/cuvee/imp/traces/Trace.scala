package cuvee.imp.traces

import cuvee.pure._

case class Update(path: Expr, rhs: Expr) {
  def free = path.free ++ rhs.free
  def funs = path.funs ++ rhs.funs

  def rename(re: Map[Var, Var]): Update =
    Update(path rename re, rhs rename re)

  def subst(su: Map[Var, Expr]): Update =
    Update(path subst su, rhs subst su)

  def inst(su: Map[Param, Type]) =
    Update(path inst su, rhs inst su)

  def map(f: Expr => Expr, g: Expr => Expr) =
    Update(path map (f, g), rhs)

  override def toString =
    if (path == True)
      "" + rhs
    else
      "if " + path + " then " + rhs
}

case class Trace(
    init: Expr,
    iteration: Iteration,
    acc: Var,
    updates: List[Update]
) extends Extra
    with Expr.bind2[Trace] {
  def typ = Sort.trace(acc.typ)
  def bound = iteration.bound + acc
  def funs = init.funs ++ iteration.funs ++ updates.flatMap(_.funs)
  def free =
    init.free ++ iteration.free ++ (Set(updates.flatMap(_.free): _*) -- bound)

  def gen = {
    // rename all bound variables
    val re = Expr.fresh(bound)
    rename(re, re, re)
  }

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Trace(
      init rename re,
      iteration rename (a, are),
      acc rename a,
      updates map (_ rename are)
    )

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Trace(
      init subst su,
      iteration subst (a, asu),
      acc rename a,
      updates map (_ subst asu)
    )

  def inst(su: Map[Param, Type]) =
    Trace(
      init inst su,
      iteration inst su,
      acc inst su,
      updates map (_ inst su)
    )

  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr =
    ???

  override def toString = {
    import cuvee.StringOps
    val f = "trace" // ^^ loop
    val u = acc + " := " + updates.mkString(" | ")
    f + "(" + init + ", for " + iteration + " do " + u + ")"
  }
}

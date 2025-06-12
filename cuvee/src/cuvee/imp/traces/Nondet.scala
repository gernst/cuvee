package cuvee.imp.traces

import cuvee.pure._

// Note, we use a choice function because we can index it easily with an integer.
// We could use arrays, but solvers may struggle to prove existence of such arrays,
// it seems more convenient to skolemize immediately.
case class Nondet(choose: Fun) extends Extra {
  val typ = choose match {
    case Fun(name, params, args, res) =>
      require(params.isEmpty)
      require(args == List(Sort.int))
      Sort.trace(res)
  }

  def free = Set()
  def funs = Set(choose)

  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
  def inst(su: Map[Param, Type]) = this
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr = ???

  override def toString =
    "nondet(" + choose.name + ")"
}

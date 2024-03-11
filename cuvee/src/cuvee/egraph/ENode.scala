package cuvee.egraph

import cuvee.pure._

sealed trait ENode {
  def args: List[EClass]
  def canon: ENode
  def isTrue: Boolean
}

case class EVar(x: Var) extends ENode {
  def args = Nil
  def canon = this
  def isTrue = false
  override def toString = x.toString
}

case class ELit(any: Any, typ: Type) extends ENode {
  def args = Nil
  def canon = this
  def isTrue = false
  override def toString = any.toString
}

case class EApp(inst: Inst, args: List[EClass]) extends ENode {
  // reminder: cannot destructively update args here,
  // because nodes are used in keys of hash maps and in sets
  def canon = EApp(inst, args map (_.find))

  def isTrue = (inst.fun == Fun.true_)

  override def toString = this match {
    case EApp(inst, Nil) =>
      inst.toString
    case _ =>
      inst + args.mkString("(", ", ", ")")
  }
}

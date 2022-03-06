package cuvee.pure

import cuvee.sexpr.Syntax

case class Inst(fun: Fun, ty: Map[Param, Type]) extends Syntax {
  require(
    ty.keySet == fun.bound,
    "some uninstantiated parameters " + ty.keySet + " for " + fun
  )

  def params =
    fun.params subst ty
  def args =
    fun.args subst ty
  def res =
    fun.res subst ty

  def apply(args: Expr*) =
    App(this, args.toList)
  def subst(su: Map[Param, Type]) =
    Inst(fun, ty map { case (p, t) => (p, t subst su) })

  def sexpr = fun.name
  override def toString = fun.name
}

case class Fun(name: String, params: List[Param], args: List[Type], res: Type) {
  def bound = params.toSet

  require(
    args.free subsetOf bound,
    "unbound parameters " + (args.free -- bound)
  )

  require(
    res.free subsetOf bound,
    "unbound parameters " + (res.free -- bound)
  )

  def apply(args: Expr*) =
    App(this, args.toList)

  def generic = {
    Inst(this, Type.fresh(params))
  }

  def paramsToString =
    params.mkString("forall ", ", ", ". ")

  def argsToString =
    args.mkString(" * ") + " -> "

  override def toString = (params, args) match {
    case (Nil, Nil) =>
      name + ": " + res
    case (Nil, _) =>
      name + ": " + argsToString + res
    case (_, Nil) =>
      name + ": " + paramsToString + res
    case _ =>
      name + ": " + paramsToString + argsToString + res
  }
}

object Fun {
  import Sort.bool
  import Sort.int

  val a = Param("a")
  val b = Param("b")

  val list_a = Sort.list(a)
  val array_a_b = Sort.array(a, b)

  val eq_ = Fun("=", List(a), List(a, a), bool)
  val ite = Fun("ite", List(a), List(bool, a, a), a)

  val select = Fun("select", List(a, b), List(array_a_b, a), b)
  val store = Fun("store", List(a, b), List(array_a_b, a, b), array_a_b)

  val nil = Fun("nil", List(a), Nil, list_a)
  val cons = Fun("cons", List(a), List(a, list_a), list_a)
  val append = Fun("append", List(a), List(list_a, list_a), list_a)

  val true_ = Fun("true", Nil, Nil, bool)
  val false_ = Fun("false", Nil, Nil, bool)
  val not = Fun("not", Nil, List(bool), bool)
  val and = Fun("and", Nil, List(bool, bool), bool)
  val or = Fun("or", Nil, List(bool, bool), bool)
  val imp = Fun("=>", Nil, List(bool, bool), bool)

  val uminus = Fun("-", Nil, List(int), int)
  val plus = Fun("+", Nil, List(int, int), int)
  val minus = Fun("-", Nil, List(int, int), int)
  val times = Fun("*", Nil, List(int, int), int)

  val le = Fun("<=", Nil, List(int, int), bool)
  val ge = Fun(">=", Nil, List(int, int), bool)
  val lt = Fun("<", Nil, List(int, int), bool)
  val gt = Fun(">", Nil, List(int, int), bool)

  def main(args: Array[String]) {
    
  }
}

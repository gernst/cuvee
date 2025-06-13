package cuvee.imp.traces

import cuvee.pure._

sealed trait Order {
  def bracket(str: String): String
}

case object Sequential extends Order {
  def bracket(str: String) = "[ " + str + " ]"
}

case object IngoreDuplicates extends Order {
  def bracket(str: String) = "⦃ " + str + " ⦄"
}

// can reorder
case object Parallel extends Order {
  def bracket(str: String) = "⟅ " + str + " ⟆"
}

// can ignore duplicates and can reorder
case object Pointwise extends Order {
  def bracket(str: String) = "{ " + str + " }"
}

// mapping the range to a multiset of values
// inserted as marker when we know that the operation is commutative and associative
// main use case are arithmetics and some bitwise operations
case class Iteration(order: Order, formals: List[LetEq]) {
  override def toString = {
    val lhs = formals.vars.mkString(", ")
    val rhs = order bracket formals.args.mkString(" | ")
    lhs + " <- " + rhs
  }

  def binds(x: Var) = {
    formals exists (_.x == x)
  }

  def iterates(it: Var) = {
    formals exists (_.e == it)
  }

  def iteratorFor(it: Var) = {
    val List(x) = formals collect { case LetEq(x, `it`) => x }
    x
  }

  def keepOnly(vars: Set[Var]) = {
    Iteration(order, formals filter { case LetEq(x, e) => vars contains x })
  }

  // for (LetEq(x, e) <- formals) {
  //   require(
  //     Sort.trace(x.typ) == e.typ,
  //     "iteration " + x + " <- " + e + " with " + x.typ + " over " + e.typ + " is ill-typed"
  //   )
  // }

  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Iteration(order, formals rename (a, re))

  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = {
    // println("iteration: " + this)
    // println(a)
    // println(su)
    Iteration(order, formals subst (a, su))
  }

  def inst(su: Map[Param, Type]) =
    Iteration(order, formals inst su)

  def map(f: Expr => Expr, g: Expr => Expr) =
    Iteration(order, formals map (_ map (f, g)))

  def bound = Set(formals map (_.x): _*)
  def free = formals.free
  def funs = formals.funs
}
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

// case class Zip(traces: List[Expr]) extends Extra {

// }

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

  // have to give up these in favor of inference
  // require(acc.typ == init.typ, "accumulator type " + acc.typ + " mismatches initializer " + init.typ)
  // for (up <- updates)
  //   require(acc.typ == up.rhs.typ, "accumulator type " + acc.typ + " mismatches update " + up + ": " + up.rhs.typ)

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Trace(
      init rename re,
      iteration rename (a, are),
      acc rename a,
      updates map (_ rename are)
    )

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Trace(
      init subst su, // XXX WRONG! su contains a, too, but initi is independent of this
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

/*
case class Mapping(
    counter: Expr,
    iteration: Iteration,
    update: Expr
) extends Extra
    with Expr.bind2[Mapping] {
  def typ = Sort.stream(update.typ)
  def bound = iteration.bound
  def funs = counter.funs ++ iteration.funs ++ update.funs
  def free = counter.free ++ iteration.free ++ (update.free -- bound)

  def map(f: Expr => Expr, g: Expr => Expr) =
    Mapping(counter map (f, g), iteration map (f, g), update map (f, g))

  def rename(a: Map[Var, Var], re: Map[Var, Var], are: Map[Var, Var]) =
    Mapping(counter rename re, iteration rename (a, are), update rename are)

  def subst(a: Map[Var, Var], su: Map[Var, Expr], asu: Map[Var, Expr]) =
    Mapping(counter subst su, iteration subst (a, asu), update subst asu)

  def inst(su: Map[Param, Type]) =
    Mapping(counter inst su, iteration inst su, update inst su)

  override def toString = {
    import cuvee.StringOps
    "map(" + counter + ", " + iteration + " | " + update + ")"
  }
}
 */

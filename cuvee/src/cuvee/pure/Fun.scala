package cuvee.pure

import cuvee.smtlib.DeclareFun
import cuvee.boogie
import cuvee.util
import cuvee.StringOps
import cuvee.util.Name

case class Inst(fun: Fun, ty: Map[Param, Type]) extends util.Syntax with boogie.Syntax {
  require(
    ty.keySet == fun.bound,
    "some uninstantiated parameters " + ty.keySet + " for " + fun
  )

  def arity =
    fun.arity
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

  val boogieOperators = boogie.Parser.translate.map(_.swap)
  def bexpr = List(boogieOperators.getOrElse(fun.name.name, fun.name))

  override def toString = fun.name.toString
}

case class Fun(name: Name, params: List[Param], args: List[Type], res: Type) {
  def bound = params.toSet
  def arity = args.length

  require(
    args.free subsetOf bound,
    "unbound parameters " + (args.free -- bound)
  )

  require(
    res.free subsetOf bound,
    "unbound parameters " + (res.free -- bound)
  )

  def rename(f: Name => Name) =
    Fun(f(name), params, args, res)

  def apply(args: Expr*) =
    App(this, args.toList)

  def default = {
    Inst(this, Type.id(params))
  }

  def generic = {
    Inst(this, Type.fresh(params))
  }

  def paramsToString =
    params.mkString("forall ", ", ", ". ")

  def argsToString =
    args.mkString(" * ") + " -> "

  def in(expr: Expr): Boolean =
    expr match {
      case _: Lit | _: Var                 => false
      case Note(expr, attr)                => this in expr
      case Is(arg, fun)                    => (fun == this) || (this in arg)
      case App(Inst(fun, _), args)         => (fun == this) || (this in args)
      case Distinct(exprs)                 => this in exprs
      case Bind(quant, formals, body, typ) => this in body
      case Let(eqs, body)                  => (eqs exists (this in _.e)) || (this in body)
    }

  def in(that: List[Expr]): Boolean =
    that exists (this in _)

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

  val unary: ((Name, List[Param], Type, Type) => Fun) = { case (name, params, arg, res) =>
    Fun(name, params, List(arg), res)
  }

  val a = Param("a")
  val b = Param("b")

  val list_a = Sort.list(a)
  val array_a_b = Sort.array(a, b)

  val eq_ = Fun("=", List(a), List(a, a), bool)
  val ite = Fun("ite", List(a), List(bool, a, a), a)

  val const = Fun("const", List(a, b), List(b), array_a_b)
  val select = Fun("select", List(a, b), List(array_a_b, a), b)
  val store = Fun("store", List(a, b), List(array_a_b, a, b), array_a_b)

  val nil = Fun("nil", List(a), Nil, list_a)
  val cons = Fun("cons", List(a), List(a, list_a), list_a)
  // val append = Fun("append", List(a), List(list_a, list_a), list_a)

  val old = Fun("old", List(a), List(a), a)
  val fin = Fun("final", List(a), List(a), a)

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
  val div = Fun("div", Nil, List(int, int), int)
  val mod = Fun("mod", Nil, List(int, int), int)

  val le = Fun("<=", Nil, List(int, int), bool)
  val ge = Fun(">=", Nil, List(int, int), bool)
  val lt = Fun("<", Nil, List(int, int), bool)
  val gt = Fun(">", Nil, List(int, int), bool)

  val builtin = Set(
    eq_,
    ite,
    select,
    store,
    true_,
    false_,
    not,
    and,
    or,
    imp,
    uminus,
    plus,
    minus,
    times,
    le,
    ge,
    lt,
    gt
  )
}

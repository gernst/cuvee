package cuvee.pure

import cuvee.StringOps
import cuvee.fail
import cuvee.trace
import cuvee.sexpr
import cuvee.util.Alpha

sealed trait Expr extends Expr.term with sexpr.Syntax {
  def typ: Type
  def inst(su: Map[Param, Type]): Expr

  def toStringTyped = toString + ": " + typ

  def unary_-(that: Expr) = App(Fun.uminus, List(this))
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)

  def and(that: Expr) = And(this, that)
  def or(that: Expr) = Or(this, that)
  def ==>(that: Expr) = Imp(this, that)

  def ===(that: Expr) = Eq(this, that)

  def ::(that: Expr) = App(Fun.cons, List(that, this))
  def ++(that: Expr) = App(Fun.append, List(this, that))
  def append(that: Expr) = App(Fun.append, List(this, that))

  def bottomup(g: Expr => Expr): Expr = {
    map(identity, g)
  }

  def topdown(f: Expr => Expr): Expr = {
    map(f, identity)
  }

  def map(f: Expr => Expr, g: Expr => Expr): Expr = {
    f(this) match {
      case lit: Lit =>
        g(lit)
      case id: Var =>
        g(id)
      case App(fun, inst, args) =>
        g(App(fun, inst, args map (_.map(f, g))))
      case Bind(quant, formals, body, typ) =>
        g(Bind(quant, formals, body.map(f, g), typ))
    }
  }
}

object Expr extends Alpha[Expr, Var] {
  val infix = Set("=", "<=", ">=", "<", ">", "+", "-", "*", "and", "or", "=>")

  def fresh(name: String, typ: Type) =
    Var(name, typ, Some(nextIndex))

  // mirror Sort.prod
  def tuple(es: List[Expr]) = es match {
    case List(e) => e
    case _       => Tuple(es)
  }

  def in(k: Int, arg: Expr, res: Type) = {
    res match {
      case Sum(args) if 0 <= k && k < args.length =>
        In(k, arg, res)
      case _ if k == 0 =>
        arg
      case _ =>
        fail("undefined: " + k + "th injection into " + res)
    }
  }
}

class VarList(vars: List[Var]) extends Expr.xs(vars) {
  def inst(su: Map[Param, Type]) = vars map (_ inst su)

  def prime = vars map (_.prime)
  def names = vars map { case Var(name, _, None) => name }
  def types = vars map (_.typ)
  def pairs = vars map { case Var(name, typ, None) => name -> typ }
  def asFormals = vars map { case x => x -> x.typ }
}

class ExprList(exprs: List[Expr]) extends Expr.terms(exprs) {
  def types = exprs map (_.typ)
  def inst(su: Map[Param, Type]) = exprs map (_ inst su)
}

case class Var(name: String, typ: Type, index: Option[Int] = None)
    extends Expr
    with Expr.x {
  def fresh(index: Int): Var =
    Var(name, typ, Some(index))
  def inst(su: Map[Param, Type]) =
    Var(name, typ subst su, index)

  def prime =
    Var(name + "^", typ, index)

  def sexpr = name ~~ index
  override def toString = name __ index
}

case class Lit(any: Any, typ: Type) extends Expr {
  def free: Set[Var] = Set()
  def rename(re: Map[Var, Var]): Expr = this
  def subst(su: Map[Var, Expr]): Expr = this
  def inst(su: Map[Param, Type]): Expr = this

  def sexpr = any
  override def toString = any.toString
}

case class Fun(name: String, params: List[Param], args: List[Type], res: Type) {
  def apply(args: Expr*) =
    App(this, args.toList)

  def gen = {
    val re = Type.fresh(params)
    Inst(args rename re, res rename re)
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

  val list = Sort.list(a)
  val array = Sort.array(a, b)

  val eq_ = Fun("=", List(a), List(a, a), bool)
  val ite = Fun("ite", List(a), List(bool, a, a), a)

  val select = Fun("select", List(a, b), List(array, a), b)
  val store = Fun("store", List(a, b), List(array, a, b), array)

  val nil = Fun("nil", List(a), Nil, list)
  val cons = Fun("cons", List(a), List(a, list), list)
  // val append = Fun("append", List(a), List(list, list), list)

  val elem = Sort(Con("Elem", 0), Nil)
  val list_elem = Sort.list(elem)
  val append = Fun("append", Nil, List(list_elem, list_elem), list_elem)

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
}

object Eq extends Sugar.binary(Fun.eq_)
object Ite extends Sugar.ternary(Fun.ite)

object Not extends Sugar.unary(Fun.not)
object Imp extends Sugar.associative(Fun.imp, Assoc.right)
object And extends Sugar.commutative(Fun.and, True, Assoc.left)
object Or extends Sugar.commutative(Fun.or, False, Assoc.left)

object UMinus extends Sugar.unary(Fun.uminus)
object Plus extends Sugar.commutative(Fun.plus, Zero, Assoc.left)
object Minus extends Sugar.associative(Fun.minus, Assoc.left)
object Times extends Sugar.commutative(Fun.times, One, Assoc.left)
// object DivBy extends Sugar.associative(Fun.divBy, Assoc.left)
// object Mod extends Sugar.associative(Fun.mod, Assoc.left)
// object Exp extends Sugar.associative(Fun.exp, Assoc.right)

object Lt extends Sugar.binary(Fun.lt)
object Le extends Sugar.binary(Fun.le)
object Gt extends Sugar.binary(Fun.gt)
object Ge extends Sugar.binary(Fun.ge)

object Forall extends Sugar.binder(Quant.forall, Sort.bool)
object Exists extends Sugar.binder(Quant.exists, Sort.bool)

case class Inst(args: List[Type], res: Type) {
  def subst(su: Map[Param, Type]) =
    Inst(args subst su, res subst su)
}

object App {
  def apply(fun: Fun, args: List[Expr]): Expr = {
    val inst = fun.gen
    val su = trace("applying " + fun + " to " + args) {
      Type.unify(inst.args, args.types, Map())
    }
    App(fun, inst subst su, args)
  }
}

case class In(k: Int, arg: Expr, typ: Type) extends Expr {
  def free = arg.free
  def rename(re: Map[Var, Var]) =
    In(k, arg rename re, typ)
  def subst(su: Map[Var, Expr]) =
    In(k, arg subst su, typ)
  def inst(su: Map[Param, Type]) =
    In(k, arg inst su, typ)

  def sexpr = ???
  override def toString =
    ("in" __ k) + "(" + arg + ")"
}

case class Tuple(args: List[Expr]) extends Expr {
  val typ = Prod(args.types)
  def free = args.free
  def rename(re: Map[Var, Var]) =
    Tuple(args rename re)
  def subst(su: Map[Var, Expr]) =
    Tuple(args subst su)
  def inst(su: Map[Param, Type]) =
    Tuple(args inst su)

  def sexpr = ???
  override def toString =
    args.mkString("(", ", ", ")")
}

case class App(fun: Fun, inst: Inst, args: List[Expr]) extends Expr {
  val typ = inst.res
  def free = args.free
  def rename(re: Map[Var, Var]) =
    App(fun, inst, args rename re)
  def subst(su: Map[Var, Expr]) =
    App(fun, inst, args subst su)
  def inst(su: Map[Param, Type]) =
    App(fun, inst subst su, args inst su)

  def sexpr = args match {
    case Nil => fun.name
    case _   => fun.name :: args
  }

  override def toString =
    (fun, args) match {
      case (_, Nil) =>
        fun.name
      case (_, List(left, right)) if Expr.infix contains fun.name =>
        "(" + left + " " + fun.name + " " + right + ")"
      case _ =>
        fun.name + args.mkString("(", ", ", ")")
    }
}

case class Quant(name: String)

object Quant {
  val exists = Quant("exists")
  val forall = Quant("forall")
  val lambda = Quant("lambda")
}

case class Bind(quant: Quant, formals: List[Var], body: Expr, typ: Type)
    extends Expr
    with Expr.bind[Bind] {
  def free = body.free -- formals
  def bound = Set(formals: _*)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Bind(quant, formals rename a, body rename re, typ)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Bind(quant, formals rename a, body subst su, typ)
  def inst(su: Map[Param, Type]) =
    Bind(quant, formals inst su, body inst su, typ subst su)

  def sexpr =
    List(quant.name, formals.asFormals, body)

  override def toString =
    quant.name + formals.map(_.toStringTyped).mkString(" ", ", ", ". ") + body
}

/*
class CaseList(cases: List[Case]) {
  def free = Set(cases flatMap (_.free): _*)
  def rename(re: Map[Var, Var]) = cases map (_ rename re)
  def subst(su: Map[Var, Expr]) = cases map (_ subst su)
  def inst(su: Map[Param, Type]) = cases map (_ inst su)
}

case class Case(pat: Expr, expr: Expr) extends Expr.bind[Case] {
  def bound = pat.free
  def free = expr.free -- pat.free
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Case(pat rename a, expr rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Case(pat rename a, expr subst su)
  def inst(su: Map[Param, Type]) =
    Case(pat inst su, expr inst su)
}

case class Match(expr: Expr, cases: List[Case], typ: Type) extends Expr {
  def free = expr.free ++ cases.free
  def rename(re: Map[Var, Var]) =
    Match(expr rename re, cases rename re, typ)
  def subst(su: Map[Var, Expr]) =
    Match(expr subst su, cases subst su, typ)
  def inst(su: Map[Param, Type]) =
    Match(expr inst su, cases inst su, typ subst su)
} */

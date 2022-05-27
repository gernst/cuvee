package cuvee.pure

import cuvee.StringOps
import cuvee.error
import cuvee.backtrack
import cuvee.trace
import cuvee.sexpr
import cuvee.util.Alpha

sealed trait Expr extends Expr.term with sexpr.Syntax {
  def typ: Type
  def inst(su: Map[Param, Type]): Expr
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr

  def toStringTyped = toString + ": " + typ

  def unary_- = UMinus(this)
  def unary_! = Not(this)
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)

  def and(that: Expr) = And(this, that)
  def or(that: Expr) = Or(this, that)
  def ==>(that: Expr) = Imp(this, that)

  def ===(that: Expr) = Eq(this, that)
  def !==(that: Expr) = Not(Eq(this, that))

  // def ::(that: Expr) = App(Fun.cons, List(that, this))
  // def ++(that: Expr) = App(Fun.append, List(this, that))
  // def append(that: Expr) = App(Fun.append, List(this, that))

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
      case App(inst, args) =>
        g(App(inst, args map (_.map(f, g))))
      case Bind(quant, formals, body, typ) =>
        g(Bind(quant, formals, body.map(f, g), typ))
    }
  }

  def replace(f: Fun, g: Fun) = bottomup {
    case App(Inst(`f`, su), args) =>
      App(Inst(g, su), args)
    case e =>
      e
  }

  def subtermOf(that: Expr): Boolean = that match {
    case _ if this == that =>
      true
    case _: Var =>
      false
    case _: Lit =>
      false
    case App(inst, args) =>
      args exists (this subtermOf _)
  }
}

object Expr extends Alpha[Expr, Var] {
  val infix =
    Set("=", "<=", ">=", "<", ">", "+", "-", "*", "and", "or", "=>", "⊕")

  def fresh(name: String, typ: Type) =
    Var(name, typ, Some(nextIndex))

  def vars(name: String, types: List[Type]) = {
    for ((t, i) <- types.zipWithIndex)
      yield Var(name, t, Some(i))
  }

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
        error("undefined: " + k + "th injection into " + res)
    }
  }

  def unify(
      pat: Expr,
      arg: Expr,
      ty: Map[Param, Type] = Map(),
      su: Map[Var, Expr] = Map()
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pat, arg) match {
      case (x: Var, _) if su contains x =>
        if (su(x) != arg)
          backtrack("cannot bind " + su(x) + " to " + arg)
        (ty, su)
      case (x: Var, _) =>
        (ty, su + (x -> arg))
      case (a: Lit, b: Lit) if a == b =>
        (ty, su)
      case (App(inst1, pats), App(inst2, args)) if inst1.fun == inst2.fun =>
        val ty_ = Type.unify(inst1.args, inst1.res, inst2.args, inst2.res, ty)
        val su_ = unify(pats, args, ty_, su)
        (ty_, su_)
      case _ =>
        backtrack("cannot bind " + pat + " to " + arg)
    }
  }

  def unify(
      pats: List[Expr],
      args: List[Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): Map[Var, Expr] = {
    (pats, args) match {
      case (Nil, Nil) =>
        su
      case (pat :: pats, arg :: args) =>
        val (ty_, su_) = unify(pat, arg, ty, su)
        unify(pats, args, ty_, su_)
      case _ =>
        backtrack("cannot unify " + pats + " with " + args)
    }
  }

  def bind(
      pat: Expr,
      arg: Expr,
      ty: Map[Param, Type] = Map(),
      su: Map[Var, Expr] = Map()
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pat, arg) match {
      case (x: Var, _) if su contains x =>
        if (su(x) != arg)
          backtrack("cannot bind " + su(x) + " to " + arg)
        (ty, su)
      case (x: Var, _) =>
        (ty, su + (x -> arg))
      case (a: Lit, b: Lit) if a == b =>
        (ty, su)
      case (App(inst1, pats), App(inst2, args)) if inst1.fun == inst2.fun =>
        val ty_ = Type.binds(inst1.args, inst1.res, inst2.args, inst2.res, ty)
        val su_ = bind(pats, args, ty_, su)
        (ty_, su_)
      case _ =>
        backtrack("cannot bind " + pat + " to " + arg)
    }
  }

  def bind(
      pats: List[Expr],
      args: List[Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): Map[Var, Expr] = {
    (pats, args) match {
      case (Nil, Nil) =>
        su
      case (pat :: pats, arg :: args) =>
        val (ty_, su_) = bind(pat, arg, ty, su)
        bind(pats, args, ty_, su_)
      case _ =>
        backtrack("cannot bind " + pats + " to " + args)
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
  def types =
    exprs map (_.typ)
  def inst(su: Map[Param, Type]) =
    exprs map (_ inst su)
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    exprs map (_ subst (ty, su))
}

case class Var(name: String, typ: Type, index: Option[Int] = None)
    extends Expr
    with Expr.x {
  def fresh(index: Int): Var =
    Var(name, typ, Some(index))
  def inst(su: Map[Param, Type]) =
    Var(name, typ subst su, index)
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    subst(
      su
    ) // no need to look at ty, it is relevant for function applications only

  def prime =
    Var(name + "^", typ, index)

  def in(that: Expr): Boolean = {
    that match {
      case that: Var =>
        this == that
      case App(_, args) =>
        args exists (this in _)
      case _ =>
        ???
    }
  }

  def in(that: List[Expr]): Boolean = {
    that exists (this in _)
  }

  def sexpr = name ~~ index
  override def toString = name __ index
}

case class Lit(any: Any, typ: Type) extends Expr {
  def free: Set[Var] = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
  def inst(su: Map[Param, Type]) = this
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) = this

  def sexpr = any
  override def toString = any.toString
}

object Eq extends Sugar.binary(Fun.eq_)
object Ite extends Sugar.ternary(Fun.ite)

object Select extends Sugar.binary(Fun.select)
object Store extends Sugar.ternary(Fun.store)

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

case class In(k: Int, arg: Expr, typ: Type) extends Expr {
  def free = arg.free
  def rename(re: Map[Var, Var]) =
    In(k, arg rename re, typ)
  def subst(su: Map[Var, Expr]) =
    In(k, arg subst su, typ)
  def inst(su: Map[Param, Type]) =
    In(k, arg inst su, typ)
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    In(k, arg subst (ty, su), typ subst ty)

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
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    Tuple(args subst (ty, su))

  def sexpr = ???
  override def toString =
    args.mkString("(", ", ", ")")
}

object Const {
  def apply(fun: Fun, typ: Type): App = {
    require(
      fun.args.isEmpty,
      "cannot instantiate non-constant" + fun
    )

    val su = Type.bind(fun.res, typ) or {
      error("cannot cast " + fun + " to " + typ)
    }

    val ps = fun.params filterNot su.contains
    require(
      ps.isEmpty,
      "unbound params casting " + fun + " to " + typ + ": " + ps
    )

    App(Inst(fun, su), Nil)
  }
}

object App {
  def apply(fun: Fun, args: List[Expr]): App = {
    require(
      fun.params.isEmpty || args.nonEmpty,
      "cannot instantiate constant " + fun
    )
    val su = Type.binds(fun.args, args.types) or {
      error("cannot apply " + fun + " to " + args)
    }

    val ps = fun.params filterNot su.contains

    require(
      ps.isEmpty,
      "unbound params applying " + fun + " to " + args + ": " + ps
    )

    App(Inst(fun, su), args)
  }

  // def apply(fun: Fun, inst: List[Type], args: List[Expr]): App = {
  //   require(
  //     fun.params.length == inst.length,
  //     "invalid instance " + inst + " for " + fun.params
  //   )

  //   val su = Type.subst(fun.params, inst)
  //   val types = fun.args subst su
  //   require(types == args.types, "cannot apply " + fun + " to " + args.types)

  //   new App(fun, inst, args)
  // }
}

case class App(inst: Inst, args: List[Expr]) extends Expr {
  def typ = inst.res
  // val su = Type.subst(fun.params, inst)

  // not satisified during parser typecheck
  // require((fun.args subst su) == args.types)
  // val typ = fun.res subst su
  def free = args.free
  def rename(re: Map[Var, Var]) =
    App(inst, args rename re)
  def subst(su: Map[Var, Expr]) =
    App(inst, args subst su)
  def inst(su: Map[Param, Type]) =
    App(inst subst su, args inst su)
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    App(inst subst ty, args subst (ty, su))

  def sexpr = args match {
    case Nil => inst
    case _   => inst :: args
  }

  override def toString =
    (inst, args) match {
      case (_, Nil) =>
        inst.toString
      case (_, List(left, right)) if Expr.infix contains inst.fun.name =>
        "(" + left + " " + inst + " " + right + ")"
      case _ =>
        inst + args.mkString("(", ", ", ")")
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
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    ??? // uh oh mess with bound variables

  def sexpr =
    List(quant.name, formals.asFormals, body)

  override def toString =
    quant.name + formals.map(_.toStringTyped).mkString(" ", ", ", ". ") + body
}

class CaseList(cases: List[Case]) {
  def free = Set(cases flatMap (_.free): _*)
  def rename(re: Map[Var, Var]) = cases map (_ rename re)
  def subst(su: Map[Var, Expr]) = cases map (_ subst su)
  def inst(su: Map[Param, Type]) = cases map (_ inst su)
}

case class Case(pat: Expr, expr: Expr)
    extends Expr.bind[Case]
    with sexpr.Syntax {
  def bound = pat.free
  def free = expr.free -- pat.free
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Case(pat rename a, expr rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Case(pat rename a, expr subst su)
  def inst(su: Map[Param, Type]) =
    Case(pat inst su, expr inst su)
  def sexpr = List(pat, expr)
}

case class Match(expr: Expr, cases: List[Case], typ: Type) extends Expr {
  def free = expr.free ++ cases.free
  def rename(re: Map[Var, Var]) =
    Match(expr rename re, cases rename re, typ)
  def subst(su: Map[Var, Expr]) =
    Match(expr subst su, cases subst su, typ)
  def inst(su: Map[Param, Type]) =
    Match(expr inst su, cases inst su, typ subst su)
  def subst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    ??? // need to fix cases, too
  def sexpr = List("match", expr, cases)
}

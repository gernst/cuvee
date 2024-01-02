package cuvee.pure

import cuvee.error
import cuvee.trace
import cuvee.boogie
import cuvee.sexpr
import cuvee.util
import cuvee.util.Alpha
import cuvee.util.Name

sealed trait Expr extends Expr.term with util.Syntax {
  def funs: Set[Fun]
  def typ: Type
  def inst(su: Map[Param, Type]): Expr
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]): Expr

  def ~~>(that: Expr) = Rule(this, that)

  def toStringTyped = toString + ": " + typ

  def unary_- = UMinus(this)
  def unary_! = Not(this)
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)

  def <=(that: Expr) = Le(this, that)
  def <(that: Expr) = Lt(this, that)

  def &&(that: Expr) = And(this, that)
  def ||(that: Expr) = Or(this, that)
  def ==>(that: Expr) = Imp(this, that)

  def ===(that: Expr) = Eq(this, that)
  def !==(that: Expr) = Not(Eq(this, that))

  // def ::(that: Expr) = App(Fun.cons, List(that, this))
  // def ++(that: Expr) = App(Fun.append, List(this, that))
  // def append(that: Expr) = App(Fun.append, List(this, that))
  def stripNotes = bottomup {
    case Note(expr, attr) => expr
    case expr             => expr
  }

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
      case Note(expr, attr) =>
        g(Note(expr.map(f, g), attr))
      case Is(arg, fun) =>
        g(Is(arg map (f, g), fun))
      case App(inst, args) =>
        g(App(inst, args map (_.map(f, g))))
      case Distinct(exprs) =>
        g(Distinct(exprs map (_.map(f, g))))
      case Let(eqs, body) =>
        g(Let(eqs map { case LetEq(x, e) => LetEq(x, e.map(f, g)) }, body.map(f, g)))
      case Bind(quant, formals, body, typ) =>
        // println("recursive map at bind, beware! " + this)
        g(Bind(quant, formals, body.map(f, g), typ))
    }
  }

  def reduce[A](g: (A, A) => A)(f: Expr => A): A = this match {
    case lit: Lit =>
      f(lit)
    case id: Var =>
      f(id)
    case App(inst, args) =>
      val as = f(this) :: (args map (_.reduce(g)(f)))
      as reduce g
    case Bind(quant, formals, body, typ) =>
      g(f(this), body.reduce(g)(f))
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
  case class CannotUnify(reason: String) extends Exception {
    override def toString = reason
  }

  case class CannotBind(pat: Expr, arg: Expr, ty: Map[Param, Type], su: Map[Var, Expr])
      extends Exception {
    override def toString = "cannot bind " + pat + " to " + arg
  }

  val infix =
    Set("<=", ">=", "<", ">", "+", "-", "*", "and", "or")
  val boogieInfix =
    boogie.Grammar.syntax.infix_ops.keySet

  def fresh(name: Name, typ: Type): Var = {
    Var(name.withIndex(nextIndex), typ)
  }

  def fresh(names: List[Name], types: List[Type]): List[Var] = {
    names zip types map { case (name, typ) =>
      Var(name.withIndex(nextIndex), typ)
    }
  }

  def vars(name: Name, types: List[Type]) = {
    for ((t, i) <- types.zipWithIndex)
      yield Var(name.withIndex(i), t)
  }

  def unify(
      expr1: Expr,
      expr2: Expr,
      ty: Map[Param, Type] = Map(),
      su: Map[Var, Expr] = Map()
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (expr1, expr2) match {
      case _ if expr1 == expr2 =>
        (ty, su)
      case (x1: Var, _) if su contains x1 =>
        unify(su(x1), expr2, ty, su)
      case (_, x2: Var) if su contains x2 =>
        unify(expr2, su(x2), ty, su)
      case (x1: Var, _) if x1 in expr2 =>
        cuvee.undefined
        throw CannotUnify("recursive unification, " + x1 + " in " + expr2)
      case (x1: Var, _) =>
        val ty_ = Type.unify(x1.typ, expr2.typ, ty)
        val su_ = su + (x1 -> expr2)
        (ty_, su_)
      case (_, x2: Var) =>
        unify(x2, expr1, ty, su)
      case (App(inst1, args1), App(inst2, args2)) if inst1.fun == inst2.fun =>
        val ty_ = Type.unify(inst1.args, inst1.res, inst2.args, inst2.res, ty)
        unify(args1, args2, ty_, su)
      case _ =>
        throw CannotUnify("cannot unify " + expr1 + " with " + expr2)
    }
  }

  def unify(
      pats: List[Expr],
      args: List[Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pats, args) match {
      case (Nil, Nil) =>
        (ty, su)
      case (pat :: pats, arg :: args) =>
        val (ty_, su_) = unify(pat, arg, ty, su)
        unify(pats, args, ty_, su_)
      case _ =>
        throw CannotUnify("cannot unify " + pats + " with " + args)
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
          throw CannotBind(pat, arg, ty, su)
        (ty, su)
      case (x: Var, _) =>
        val ty_ = Type.bind(x.typ, arg.typ, ty)
        (ty_, su + (x -> arg))
      case (a: Lit, b: Lit) if a == b =>
        (ty, su)
      case (App(inst1, pats), App(inst2, args)) if inst1.fun == inst2.fun =>
        val ty_ = Type.binds(inst1.args, inst1.res, inst2.args, inst2.res, ty)
        val (ty__, su_) = bind(pats, args, ty_, su)
        (ty__, su_)
      case _ =>
        throw CannotBind(pat, arg, ty, su)
    }
  }

  def bind(
      pats: List[Expr],
      args: List[Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pats, args) match {
      case (Nil, Nil) =>
        (ty, su)
      case (pat :: pats, arg :: args) =>
        val (ty_, su_) = bind(pat, arg, ty, su)
        bind(pats, args, ty_, su_)
    }
  }
}

class ExprList(exprs: List[Expr]) extends Expr.terms(exprs) {
  def types =
    exprs map (_.typ)
  def funs =
    Set(exprs flatMap (_.funs): _*)
  def inst(su: Map[Param, Type]) =
    exprs map (_ inst su)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    exprs map (_ inst (ty, su))
  def replace(f: Fun, g: Fun) =
    exprs map (_ replace (f, g))
}

case class Var(name: Name, typ: Type) extends Expr with Expr.x {
  def funs = Set()
  def fresh(index: Int): Var =
    Var(name.withIndex(index), typ)
  def inst(su: Map[Param, Type]) =
    Var(name, typ subst su)

  // no need to look at ty, it is relevant for function applications only
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    subst(su)

  /** Skolemize this variable, transferring it to a constant function without parameters.
    *
    * @return
    *   Function that represents the variable
    */
  def skolem: Fun = Fun(name, Nil, Nil, typ)

  def prime: Var =
    Var(name.withName(name.name + "^"), typ)

  def in(that: Expr): Boolean =
    that match {
      case that: Var        => this == that
      case App(_, args)     => this in args
      case _: Lit           => false
      case Distinct(exprs)  => this in exprs
      case Is(arg, fun)     => this in arg
      case Note(expr, attr) => this in expr
      case self @ Let(eqs, body) =>
        val bound = self.bound
        (eqs exists (this in _.e)) || ((this in body) && !(bound contains this))
      case Bind(quant, formals, body, typ) =>
        (this in body) && !(formals contains this)
    }

  def in(that: Prop): Boolean =
    that match {
      case Atom(expr, cex) =>
        this in expr

      case Disj(xs, assms, concls) =>
        (assms exists (this in _)) || (concls exists (this in _))
    }

  def in(that: Conj): Boolean =
    that match {
      case Conj(xs, props) =>
        (props exists (this in _))
    }

  def in(that: List[Expr]): Boolean =
    that exists (this in _)

  override def toString = name.toString
}

class VarList(vars: List[Var]) extends Expr.xs(vars) {
  def inst(su: Map[Param, Type]) = vars map (_ inst su)

  def prime = vars map (_.prime)
  def names = vars map { case Var(name, _) => name }
  def types = vars map (_.typ)
  def pairs = vars map { case Var(name, typ) => name -> typ }
  def asFormals = vars map { case x => x -> x.typ }
  def asScope = vars map { case x @ Var(name, typ) => name -> x }

  def toStringTyped = vars.map(_.toStringTyped).mkString(", ")
}

class VarSet(vars: Set[Var]) {
  def asScope = vars map { case x @ Var(name, typ) => name -> x }
}

case class Lit(any: Any, typ: Type) extends Expr {
  def funs = Set()
  def free = Set()
  def rename(re: Map[Var, Var]) = this
  def subst(su: Map[Var, Expr]) = this
  def inst(su: Map[Param, Type]) = this
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) = this

  override def toString = any.toString
}

object Eq extends Sugar.binary(Fun.eq_) {
  def apply(pairs: Iterable[(Expr, Expr)]): List[Expr] = {
    for ((a, b) <- pairs.toList)
      yield Eq(a, b)
  }

  def apply(left: List[Expr], right: List[Expr]): List[Expr] = {
    require(
      left.length == right.length,
      "invalid equation between mismatching arguments: " + left + " and " + right
    )

    for ((a, b) <- left zip right)
      yield Eq(a, b)
  }
}

object Ite extends Sugar.ternary(Fun.ite)

object Old extends Sugar.pointwise(Fun.old)
object Final extends Sugar.pointwise(Fun.fin)

object Const extends Sugar.unary(Fun.const)
object Select extends Sugar.binary(Fun.select)
object Store extends Sugar.ternary(Fun.store)

object Not extends Sugar.unary(Fun.not) {
  def apply(args: List[Expr]) =
    args map this
}

object Imp extends Sugar.associative(Fun.imp, Assoc.right)
object And extends Sugar.commutative(Fun.and, True, Assoc.left)
object Or extends Sugar.commutative(Fun.or, False, Assoc.left)

object UMinus extends Sugar.unary(Fun.uminus)
object Plus extends Sugar.commutative(Fun.plus, Zero, Assoc.left)
object Minus extends Sugar.associative(Fun.minus, Assoc.left)
object Times extends Sugar.commutative(Fun.times, One, Assoc.left)
object DivBy extends Sugar.associative(Fun.div, Assoc.left)
object Mod extends Sugar.associative(Fun.mod, Assoc.left)
// object Exp extends Sugar.associative(Fun.exp, Assoc.right)

object Succ {
  def apply(expr: Expr) = {
    Plus(expr, One)
  }

  def unapply(expr: Expr) = expr match {
    case Plus(List(arg, One)) => Some(arg)
    case Plus(List(One, arg)) => Some(arg)
    case _                    => None
  }
}

object Lt extends Sugar.binary(Fun.lt)
object Le extends Sugar.binary(Fun.le)
object Gt extends Sugar.binary(Fun.gt)
object Ge extends Sugar.binary(Fun.ge)

object Forall extends Sugar.binder(Quant.forall, Sort.bool)
object Exists extends Sugar.binder(Quant.exists, Sort.bool)

case class Is(arg: Expr, fun: Fun) extends Expr {
  def typ = Sort.bool
  def funs = arg.funs
  def free = arg.free
  def rename(re: Map[Var, Var]) =
    Is(arg rename re, fun)
  def subst(su: Map[Var, Expr]) =
    Is(arg subst su, fun)
  def inst(su: Map[Param, Type]) =
    Is(arg inst su, fun)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    Is(arg inst (ty, su), fun)

  override def toString = {
    arg + " is " + fun.name
  }
}

object App extends ((Inst, List[Expr]) => App) {
  def apply(inst: Inst, args: List[Expr]): App = {
    require(
      inst.args == args.types,
      "cannot apply " + inst.fun + " with " + inst.args + " to " + args + " with " + args.types
    )
    new App(inst, args)
  }

  def apply(fun: Fun, args: List[Expr]): App = {
    require(
      fun.params.isEmpty || args.nonEmpty,
      "cannot instantiate constant " + fun
    )

    val inst = fun.generic

    // println("infer: " + fun + " to " + (args map (_.typ)))
    // println(inst.ty)
    // println(inst.args, args.types, inst.ty)
    val su = trace(
      "typing failed: " + fun + " " + args.mkString(", ") + ": " + args.types.mkString(", ")
    ) {
      Type.binds(inst.args, args.types)
    }
    // println("result: " + su)

    val ps = inst.ty filterNot { case (a, b: Param) =>
      su contains b
    }

    require(
      ps.isEmpty,
      "unbound params applying " + fun + " to " + args + ": " + ps
    )

    val expr = new App(inst, args)

    expr inst su
  }

  def apply(fun: Fun, typ: Type): App = {
    require(
      fun.args.isEmpty,
      "cannot instantiate non-constant" + fun
    )
    val su = trace(
      "typing failed: " + fun + " as " + typ
    ) {
      Type.bind(fun.res, typ)
    }

    val ps = fun.params filterNot su.contains
    require(
      ps.isEmpty,
      "unbound params casting " + fun + " to " + typ + ": " + ps.mkString(
        ", "
      ) + " with inst: " + su
    )

    new App(Inst(fun, su), Nil)
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
  // require(
  //   inst.args == args.types,
  //   f"The actual arguments' types don't match the function parameter types.\noffending function: ${inst.fun}"
  // )

  def funs = args.funs + inst.fun
  def fun = inst.fun
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
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    App(inst subst ty, args inst (ty, su))

  override def toString = this match {
    // Constants
    case App(inst, Nil) => inst.toString
    // Logical connectives
    case And(phis) => phis mkString ("(", " && ", ")")
    case Or(phis)  => phis mkString ("(", " || ", ")")
    // Iff (<==>), needs special handling, as this is also represented by "=" internally
    case Eq(lhs, rhs) if lhs.typ == Sort.bool =>
      "(" + lhs + " <==> " + rhs + ")"
    case Eq(lhs, rhs) =>
      "(" + lhs + " == " + rhs + ")"
    case Imp(phi, psi) =>
      "(" + phi + " ==> " + psi + ")"
    case DivBy(lhs, rhs) =>
      "(" + lhs + " / " + rhs + ")"
    case Mod(lhs, rhs) =>
      "(" + lhs + " % " + rhs + ")"
    case Ite(test, left, right) =>
      "(if " + test + " then " + left + " else " + right + ")"
    // Infix operators
    case App(_, List(lhs, rhs)) if Expr.boogieInfix contains inst.fun.name.name =>
      "(" + lhs + " " + inst.toString + " " + rhs + ")"
    // Unary -
    case Not(psi)    => "! (" + psi + ")"
    case UMinus(arg) => "- (" + arg + ")"
    // Map access
    case Select(arr, idx)        => arr + "[" + idx + "]"
    case Store(arr, idx, newval) => arr + "[" + idx + ":=" + newval + "]"
    // Applications (i.e. function calls)
    case App(_, args) => inst + (args mkString ("(", ", ", ")"))
  }
}

case class Quant(name: String) {
  override def toString = name
}

object Quant {
  val exists = Quant("exists")
  val forall = Quant("forall")
  val lambda = Quant("lambda")
}

case class Bind(quant: Quant, formals: List[Var], body: Expr, typ: Type)
    extends Expr
    with Expr.bind[Bind] {

  require(bound.nonEmpty)

  def funs = body.funs
  def free = body.free -- formals
  def bound = Set(formals: _*)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Bind(quant, formals rename a, body rename re, typ)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Bind(quant, formals rename a, body subst su, typ)
  def inst(su: Map[Param, Type]) =
    Bind(quant, formals inst su, body inst su, typ subst su)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    cuvee.undefined // uh oh mess with bound variables

  def refreshAll = {
    val re = Expr.fresh(formals)
    rename(re)
  }

  override def toString =
    quant.name + formals.map(_.toStringTyped).mkString(" ", ", ", " :: ") + body
}

class CaseList(cases: List[Case]) {
  def free = Set(cases flatMap (_.free): _*)
  def funs = Set(cases flatMap (_.funs): _*)
  def rename(re: Map[Var, Var]) = cases map (_ rename re)
  def subst(su: Map[Var, Expr]) = cases map (_ subst su)
  def inst(su: Map[Param, Type]) = cases map (_ inst su)
}

case class Case(pat: Expr, expr: Expr) extends Expr.bind[Case] with util.Syntax {

  def funs = pat.funs ++ expr.funs
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
  def funs = expr.funs ++ cases.funs
  def free = expr.free ++ cases.free
  def rename(re: Map[Var, Var]) =
    Match(expr rename re, cases rename re, typ)
  def subst(su: Map[Var, Expr]) =
    Match(expr subst su, cases subst su, typ)
  def inst(su: Map[Param, Type]) =
    Match(expr inst su, cases inst su, typ subst su)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    cuvee.undefined // need to fix cases, too
}

class LetEqList(eqs: List[LetEq]) {
  def vars = eqs map (_.x)
  def args = eqs map (_.e)
  def bound = Set(eqs map (_.bound): _*)
  def free = Set(eqs flatMap (_.free): _*)
  def funs = Set(eqs flatMap (_.funs): _*)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) = eqs map (_ rename (a, re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = eqs map (_ subst (a, su))
  def inst(su: Map[Param, Type]) = eqs map (_ inst su)
}

case class LetEq(x: Var, e: Expr) extends util.Syntax {
  def bound = x
  def free = e.free
  def funs = e.funs
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    LetEq(x rename a, e rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    LetEq(x rename a, e subst su)
  def inst(su: Map[Param, Type]) =
    LetEq(x inst su, e inst su)

  def toEq = Eq(x, e)
}

case class Let(eqs: List[LetEq], body: Expr) extends Expr with Expr.bind[Let] {
  def bound = eqs.bound
  def free = eqs.free ++ (body.free -- bound)
  def funs = eqs.funs ++ body.funs
  def typ = body.typ

  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Let(eqs rename (a, re), body rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Let(eqs subst (a, su), body subst su)
  def inst(su: Map[Param, Type]) =
    Let(eqs inst su, body inst su)

  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    cuvee.undefined // need to fix let eqs, too
}

case class Note(expr: Expr, attr: List[sexpr.Expr]) extends Expr {
  def typ = expr.typ

  def free = expr.free
  def funs = expr.funs

  def rename(re: Map[Var, Var]) =
    Note(expr rename re, attr)
  def subst(su: Map[Var, Expr]) =
    Note(expr subst su, attr)
  def inst(su: Map[Param, Type]) =
    Note(expr inst su, attr)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    Note(expr inst (ty, su), attr)
}

case class Distinct(exprs: List[Expr]) extends Expr {
  def typ = Sort.bool

  def free = exprs.free
  def funs = exprs.funs

  def rename(re: Map[Var, Var]) =
    Distinct(exprs rename re)
  def subst(su: Map[Var, Expr]) =
    Distinct(exprs subst su)
  def inst(su: Map[Param, Type]) =
    Distinct(exprs inst su)
  def inst(ty: Map[Param, Type], su: Map[Var, Expr]) =
    Distinct(exprs inst (ty, su))
}

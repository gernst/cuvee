package cuvee.boogie

import arse._

import scala.util.DynamicVariable

import cuvee._
import cuvee.State
import cuvee.backend._
import cuvee.pure._
import cuvee.imp._
import cuvee.util.Name
import cuvee.smtlib.Cmd
import cuvee.smtlib.Assert
import cuvee.smtlib.DeclareFun
import cuvee.smtlib.DefineFun
import cuvee.smtlib.DeclareSort
import cuvee.smtlib.DefineSort
import cuvee.smtlib.Lemma
import cuvee.smtlib.DeclareDatatypes
import cuvee.smtlib.DeclareProc
import cuvee.smtlib.DefineProc

object Parser {
  def kw(name: String) = KW(name)
  val eof = new Token {}
  val id = V[String]
  val op = V[String]
  val number = V[String]
  val string = V[String]
  val quant = V[String]

  object toplevel {
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()
  }

  object stack extends DynamicVariable(State.default) {
    def within[A](p: Parser[A, Token]) =
      S(p, this)
  }

  def state = stack.value

  val a = Param("a")
  val old = state.fun("old", List(a), List(a), a)

  val translate = Map(
    "<==>" -> "=",
    "==>" -> "=>",
    "&&" -> "and",
    "||" -> "or",
    "==" -> "=",
    // "!=" -> "distinct",
    "/" -> "div",
    "%" -> "mod",
    "!" -> "not"
  )

  object typing extends Scope[Param, Type] {
    def unify(typ1: Type, typ2: Type) = {
      value = Type.unify(typ1, typ2, value)
    }

    def unify(types1: List[Type], types2: List[Type]) = {
      value = Type.unify(types1, types2, value)
    }

    def app(name: Name, args: List[Expr]) = {
      val arity = args.length
      require(
        state.funs contains (name, arity),
        "no such function: " + (name, arity) + " in " + state.funs.keys
      )
      val fun = state funs (name, arity)
      val inst = fun.generic
      unify(inst.args, args.types)
      App(inst, args)
    }

    def bind(
        name: Name,
        bound: List[Var],
        body: Expr,
        typ: Type
    ) = {
      val quant = Quant(name.name)
      unify(body.typ, typ)
      Bind(quant, bound, body, typ)
    }

    def resolved(arg: Expr) = {
      arg inst value
    }

    def checked(arg: Expr, typ: Type) = {
      trace("checking\n  " + arg + ":\n    " + typ) {
        unify(arg.typ, typ)
        arg inst value
      }
    }
  }

  def make_sort(ctx: Map[Name, Param]): ((Name, List[Type]) => Type) = {
    case (name, Nil) if ctx contains name =>
      ctx(name)
    case (name, args) if state.cons contains name =>
      Sort(state.cons(name), args)
  }

  def make_op: ((String, List[Expr]) => Expr) = {
    case ("!=", List(arg1, arg2)) =>
      Not(Eq(arg1, arg2))

    case (name, args) if translate contains name =>
      val name_ = translate(name)
      typing.app(name_, args)

    case (name, args) =>
      typing.app(name, args)
  }

  val make_expr: (Expr => Expr) =
    arg => typing.resolved(arg)

  def make_typed_expr(typ: Type): (Expr => Expr) =
    (arg) => typing.checked(arg, typ)

  val make_formula: (Expr => Expr) =
    arg => typing.checked(arg, Sort.bool)

  def make_app(scope: Map[Name, Var]): ((Name, List[Expr]) => Expr) = {
    case (name, Nil) if scope contains name =>
      scope(name)
    case (name, args) if state.funs contains (name, args.length) =>
      typing.app(name, args)
    case (name, Nil) =>
      error("unknown variable or constant: " + name)
    case (name, args) =>
      error("unknown function: " + name + " with arity " + args.length)
  }

  def make_var(scope: Map[Name, Var]): (Name => Var) = {
    case name if scope contains name =>
      scope(name)
    case name =>
      error(s"unknown variable: ${name.toString}")
  }

  def make_bind: ((String, (List[Var], Expr)) => Expr) = {
    case (name, (bound, body)) =>
      typing.bind(name, bound, body, Sort.bool)
  }

  val define_sort: ((Name, List[Param], Option[Type]) => Cmd) = {
    case (name, params, None) =>
      val arity = params.length
      state.con(name, arity)
      DeclareSort(name, arity)

    case (name, params, Some(typ)) =>
      val arity = params.length
      state.con(name, arity)
      state.condef(name, params, typ)
      DefineSort(name, params, typ)
  }

  val define_fun: ((Name, (List[Var], (Type, Option[Expr]))) => Cmd) = {
    case (name, (args, (typ, None))) =>
      state.fun(name, Nil, args.types, typ)
      DeclareFun(name, args.types, typ)

    case (name, (args, (typ, Some(body)))) =>
      state.fun(name, Nil, args.types, typ)
      state.fundef(name, args, body)
      DefineFun(name, args, typ, body, body.funs exists (_.name == name))
  }

  val define_proc: ((Name, ((List[Var], List[Var]), (Option[Spec], Option[Prog]))) => Cmd) = {
    case (name, ((in, out), (spec, None))) =>
      state.proc(name, Nil, in.types, out.types, spec)
      DeclareProc(name, in.types, out.types)

    case (name, ((in, out), (spec, Some(body)))) =>
      state.proc(name, Nil, in.types, out.types, spec)
      state.procdef(name, in, out, body)
      DefineProc(name, in, out, spec, body)
  }

  def make_constr
      : ((Name, List[Param], List[Fun], Type) => (Fun, List[Fun])) = {
    case (name, params, sels, res) =>
      // declare the constructor
      state.fun(name, params, sels map (_.res), res)
      // declare projections for the selectors
      for (sel <- sels) {
        state.fun(sel.name, sel.params, sel.args, sel.res)
      }

      (Fun(name, params, sels map (_.res), res), sels)
  }

  def make_datatype: (((Name, List[Param]), List[(Fun, List[Fun])]) => Cmd) = {
    case ((name, params), constrs) =>
      val arity = params.length
      val dt = Datatype(params, constrs)
      state.datatype(name, dt)
      DeclareDatatypes(List((name, arity)), List(dt))
  }

  val make_script: (List[Cmd] => (List[Cmd], State)) = { case cmds =>
    (cmds, state)
  }
}

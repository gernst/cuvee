package cuvee.boogie

import easyparse._

import scala.util.DynamicVariable

import cuvee._
import cuvee.State
import cuvee.pure._
import cuvee.imp._
import cuvee.imp.traces._
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
import cuvee.smtlib.DeclareVar
import cuvee.smtlib.DeclareAbstractions
import cuvee.smtlib.DeclareContracts
import cuvee.prove.Tactic
import cuvee.sexpr.Attrs
import cuvee.prove.Proof

class Parser(val state: State) {
  object toplevel {
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()
  }

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

      trace("cannot apply " + fun + " to " + args + " with types " + args.types) {
        unify(inst.args, args.types)
      }

      new App(inst, args)
    }

    def at(name: String, arg: Expr) = {
      val loc = Loc(name)
      new At(loc, arg)
    }

    def bind(
        name: String,
        bound: List[Var],
        body: Expr,
        typ: Type
    ) = {
      val quant = Quant(name)
      unify(body.typ, typ)
      Bind(quant, bound, body, typ)
    }

    // named tr to avoid clash with cuvee.trace
    def tr(init: Expr, iteration: Iteration, acc: Var, updates: List[Update]) = {
      unify(acc.typ, init.typ) // prefer init's type

      for (LetEq(x, e) <- iteration.formals) {
        unify(Sort.trace(x.typ), e.typ)
      }

      for (Update(path, rhs) <- updates) {
        unify(path.typ, Sort.bool)
        unify(rhs.typ, init.typ)
      }

      new Trace(init, iteration, acc, updates)
    }

    def mp(iteration: Iteration, result: Expr) = {
      for (LetEq(x, e) <- iteration.formals) {
        unify(Sort.trace(x.typ), e.typ)
      }

      new Mapping(iteration, result)
    }

    def resolved(arg: Expr) = {
      val su = Type.prune(value)
      arg inst su
    }

    def checked(arg: Expr, typ: Type) = {
      trace("checking\n  " + arg + ":\n    " + typ) {
        unify(arg.typ, typ)
        resolved(arg)
      }
    }
  }

  def make_sort(ctx: Map[Name, Param]): ((Name, List[Type]) => Type) = {
    case (name, Nil) if ctx contains name =>
      ctx(name)
    case (name, args) if state.cons contains name =>
      Sort(state.cons(name), args)
    case (name, Nil) =>
      cuvee.error("unknown sort: " + name)
    case (name, args) =>
      println(state.cons)
      cuvee.error("unknown sort: " + name + args.mkString("<", ",", ">"))
  }

  def make_op: ((String, List[Expr]) => Expr) = {
    case ("!=", List(arg1, arg2)) =>
      make_not(make_eq(arg1, arg2))

    case (name, args) if Grammar.translate contains name =>
      val name_ = Grammar.translate(name)
      typing.app(name_, args)

    case (name, args) =>
      typing.app(name, args)
  }

  val make_expr: (Expr => Expr) =
    arg => typing.resolved(arg)

  def make_typed_expr(typ: Type): (Expr => Expr) =
    arg => typing.checked(arg, typ)

  val make_formula: (Expr => Expr) =
    arg => typing.checked(arg, Sort.bool)

  def make_app(scope: Map[Name, Var]): ((Name, List[Expr]) => Expr) = {
    case (name, Nil) if scope contains name =>
      scope(name)
    case (name, args) if state.funs contains (name, args.length) =>
      // println("apply " + name + " to " + args)
      typing.app(name, args)
    case (name, Nil) =>
      error("unknown variable or constant: " + name + " in " + scope)
    case (name, args) =>
      error("unknown function: " + name + " with arity " + args.length)
  }

  val make_fun_ref: ((Name, Option[BigInt]) => (Name, Int)) = {
    // Names may become non-unique in the future. Thus make it possible to specify the arity
    // of a function.
    case (name, Some(arity)) =>
      (name, arity.toInt)

    case (name, None) =>
      val candidates = state.funs.filter(_._1._1 == name)

      if (candidates.size < 1)
        error(f"No function named ${name} found.")
      if (candidates.size > 1)
        error(
          f"Multiple functions named ${name} found. Please specify the arity as follows: ${name}[<arity>]"
        )

      candidates.keys.head
  }

  def make_var(scope: Map[Name, Var]): (Name => Var) = {
    case name if scope contains name =>
      scope(name)
    case name if state.vars contains name =>
      state.vars(name)
    case name =>
      error(s"unknown variable: ${name.toString}")
  }

  def make_bind: ((String, (List[Var], Expr)) => Expr) = { case (name, (bound, body)) =>
    typing.bind(name, bound, body, Sort.bool)
  }

  def make_at: (((String, Expr)) => Expr) = { case (loc, arg) =>
    typing.at(loc, arg)
  }

  def make_not =
    (arg: Expr) => typing.app("not", List(arg))
  def make_eq =
    (left: Expr, right: Expr) => typing.app("=", List(left, right))
  def make_select =
    (base: Expr, index: Expr) => typing.app("select", List(base, index))
  def make_select_ =
    (base: Expr, index: Expr) => typing.app("select_", List(base, index))
  def make_store =
    (base: Expr, index: Expr, value: Expr) => typing.app("store", List(base, index, value))
  def make_ite =
    (test: Expr, left: Expr, right: Expr) => typing.app("ite", List(test, left, right))

  def make_iteration: (List[Var], (List[Expr], Order)) => Iteration = {
    case (vars, (exprs, order)) =>
      require(vars.length == exprs.length)
      val formals =
        for ((x, e) <- (vars zip exprs))
          yield LetEq(x, e)
      Iteration(order, formals)
  }

  def make_mapping: (Iteration, Expr) => Expr = { case (iteration, result) =>
    typing.mp(iteration, result)
  }

  def make_trace: (Expr, (Iteration, (Var, List[Update]))) => Expr = {
    case (init, (iteration, (acc, updates))) =>
      typing.tr(init, iteration, acc, updates)
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

  val declare_var: ((Name ~ Type) => Cmd) = { case (name ~ typ) =>
    state global (name, typ)
    DeclareVar(name, typ)
  }

  val define_fun: ((Name ~ List[Param] ~ (List[Var] ~ Type ~ Option[Expr])) => Cmd) = {
    case (name ~ params ~ (args ~ typ ~ None)) =>
      // state.fun(name, Nil, args.types, typ)
      DeclareFun(name, params, args.types, typ)

    case (name ~ params ~ (args ~ typ ~ Some(body))) =>
      // state.fun(name, Nil, args.types, typ)
      state.fundef(name, args, body)
      DefineFun(name, params, args, typ, body, body.funs exists (_.name == name))
  }

  val define_proc: (
      (
          Name ~ List[Param],
          ((List[Var] ~ List[Var] ~ List[Var]), (Option[Spec], Option[Prog]))
      ) => Cmd
  ) = {
    case (name ~ params, (in ~ out ~ mod, (spec, None))) =>
      state.proc(name, params, in, out, spec)
      DeclareProc(name, params, in, out, spec)

    case (name ~ params, (in ~ out ~ mod, (spec, Some(body)))) =>
      state.proc(name, params, in, out, spec)
      state.procdef(name, params, in, out, body)
      DefineProc(name, params, in, out, spec, body)
  }

  val define_contract: (Name ~ List[Param], List[(Mode, Var)] ~ List[(Expr, Expr)]) => Cmd = {
    case (name ~ params, (formals, pairs)) =>
      state.contract(name, params, formals, pairs)
      DeclareContracts(name, params, formals, pairs)
  }

  def make_constr: ((Name, List[Param], List[Fun], Type) => (Fun, List[Fun])) = {
    case (name, params, sels, res) =>
      // declare the constructor
      val args = sels map (_.res)
      val fun = state.fun(name, params, args, res)
      // println("declaring constructor: " + fun)

      // declare projections for the selectors
      for (sel <- sels) {
        val fun = state.fun(sel.name, sel.params, sel.args, sel.res)
        // println("declaring selector: " + fun)
      }

      (fun, sels)
  }

  def make_call: (((List[Var], Name), List[Expr])) => Call = { case ((out, name), in) =>
    Call(name, in, out)
  }

  def make_datatype: (((Name, List[Param]), List[(Fun, List[Fun])]) => Cmd) = {
    case ((name, params), constrs) =>
      val arity = params.length
      val dt = Datatype(params, constrs)
      state.datatype(name, dt)
      DeclareDatatypes(List((name, arity)), List(dt))
  }

  def make_datatypes: (List[((Name, List[Param]), List[(Fun, List[Fun])])] => Cmd) = { case descr =>
    val stuff = for (((name, params), constrs) <- descr) yield {
      val arity = params.length
      val dt = Datatype(params, constrs)
      state.datatype(name, dt)
      (name, arity) -> dt
    }

    val (arities, dts) = stuff.unzip
    DeclareDatatypes(arities, dts)
  }

  def make_abstraction: (((Name, List[Param]), List[(Fun, List[Fun])]) => Cmd) = {
    case ((name, params), constrs) =>
      val arity = params.length
      val dt = Datatype(params, constrs)
      state.abstraction(name, dt)
      DeclareAbstractions(List((name, arity)), List(dt))
  }

  def make_abstractions: (List[((Name, List[Param]), List[(Fun, List[Fun])])] => Cmd) = {
    case descr =>
      val stuff = for (((name, params), constrs) <- descr) yield {
        val arity = params.length
        val dt = Datatype(params, constrs)
        state.abstraction(name, dt)
        (name, arity) -> dt
      }

      val (arities, dts) = stuff.unzip
      DeclareAbstractions(arities, dts)
  }

  val make_lemma: (
      Option[smtlib.Mode],
      List[(sexpr.Kw, Option[sexpr.Expr])],
      (Expr, Option[Proof])
  ) => Lemma = { case (mode, attrs, (expr, tactic)) =>
    Lemma(expr, tactic, mode, Attrs(attrs))
  }

  val make_script: (List[Cmd] => (List[Cmd], State)) = { case cmds =>
    (cmds, state)
  }

  val merge = (specs: List[Spec]) => {
    val xs = specs flatMap (_.xs)
    val pre = And(specs flatMap (s => And.flattenStrong(s.pre)))
    val post = And(specs flatMap (s => And.flattenStrong(s.post)))
    Spec(xs, pre, post)
  }

  def maybe_merge(mod: List[Var]) = (specs: List[Spec]) => {
    if (mod.isEmpty && specs.isEmpty) {
      None
    } else {
      val xs = specs flatMap (_.xs)
      val pre = And(specs flatMap (s => And.flattenStrong(s.pre)))
      val post = And(specs flatMap (s => And.flattenStrong(s.post)))
      val spec = Spec(mod ++ xs, pre, post)
      Some(spec)
    }
  }
}

object Parser {
  def kw(name: String) = KW(name)
  val eof = new Token {}
  val id = V[String]
  val op = V[String]
  val number = V[String]
  val string = V[String]
  val quant = V[String]
  val loc = V[String]

  val final_to_old: (Expr => Expr) =
    (expr: Expr) => final_to_old_(expr, Set())

  def final_to_old_(expr: Expr, bound: Set[Var]): Expr = expr match {
    case l: Lit =>
      l
    case x: Var if !(bound contains x) =>
      Old(x)
    case x: Var =>
      x
    case Final(expr) =>
      expr
    case App(inst, args) =>
      App(inst, args map (final_to_old_(_, bound)))
    case Bind(quant, formals, body, typ) =>
      Bind(quant, formals, final_to_old_(body, bound ++ formals), typ)
  }

  val old_to_final: (Expr => Expr) =
    (expr: Expr) => old_to_final_(expr, Set())

  def old_to_final_(expr: Expr, bound: Set[Var]): Expr = expr match {
    case l: Lit =>
      l
    case x: Var if !(bound contains x) =>
      Final(x)
    case x: Var =>
      x
    case Old(expr) =>
      expr
    case App(inst, args) =>
      App(inst, args map (old_to_final_(_, bound)))
    case Bind(quant, formals, body, typ) =>
      Bind(quant, formals, old_to_final_(body, bound ++ formals), typ)
  }
}

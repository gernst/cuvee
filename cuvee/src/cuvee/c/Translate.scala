package cuvee.c

import cuvee.SetOps
import cuvee.State
import cuvee.pure
import cuvee.imp
import cuvee.smtlib
import scala.collection.immutable
import cuvee.pure.Sort

object Translate {
  var split = false
  var translateAsserts = true
  var assumeBounds = false
  val (prelude, state) = cuvee.boogie.parse("cuvee/src/cuvee/c/c.bpl")
}

class Translate(state: State) {
  val Void = state.sort("c#void", Nil)
  val void = state.funs("c#void", 0)()
  // val heap = state.vars("c#heap")
  val bitand = state.funs("c#bitand", 2)
  val bitor = state.funs("c#bitor", 2)
  val bitxor = state.funs("c#bitxor", 2)

  def ptr(typ: Type) =
    state.sort("c#ptr", List(resolve(typ)))

  def result(typ: Type) =
    pure.Var("c#result", resolve(typ))

  var vars: Map[String, pure.Var] = Map()
  var funs: Map[String, (List[Formal], Type)] = Map()

  def default(typ: Type) = typ match {
    case _: Signed | _: Unsigned =>
      List(pure.Zero)
    case Type._Bool =>
      List(pure.False)
    case _ =>
      List()
  }

  def bounds(x: pure.Var, typ: Type) = typ match {
    case Type._Bool =>
      pure.True

    case Type._float | Type._double =>
      pure.True

    case Signed(name, bytes) =>
      val exp = BigInt(1) << (bytes * 8 - 1)
      val min = pure.Lit(-exp, pure.Sort.int)
      val max = pure.Lit(exp, pure.Sort.int)
      (min <= x) && (x < max)

    case Unsigned(name, bytes) =>
      val exp = BigInt(1) << (bytes * 8)
      val min = pure.Zero
      val max = pure.Lit(exp, pure.Sort.int)
      (min <= x) && (x < max)

    case _ =>
      ???
  }

  def init(stmts: List[Stmt], scope: Map[String, pure.Var]): List[imp.Prog] =
    for (
      stmt <- stmts;
      prog <- init(stmt, scope)
    )
      yield prog

  def init(stmt: Stmt, scope: Map[String, pure.Var]): List[imp.Prog] = stmt match {
    case VarDef(Formal(typ, name), None) =>
      val x = scope(name)
      val asg_ = imp.Assign(List(x), default(typ))
      List(asg_)

    case VarDef(Formal(typ, name), Some(expr)) =>
      val x = scope(name)
      val (rhs_, progs) = eval(expr, scope)
      val asg_ = imp.Assign(List(x), List(rhs_))
      progs ++ List(asg_)

    case Group(stmts) =>
      init(stmts, scope)

    case _ =>
      Nil
  }

  def globals(stmts: List[Stmt]): List[smtlib.Cmd] =
    for (
      stmt <- stmts;
      prog <- global(stmt, stmts)
    )
      yield prog

  def global(stmt: Stmt, all: List[Stmt]): List[smtlib.Cmd] = stmt match {
    case TypeDef(typ, name) =>
      val typ_ = resolve(typ)
      state.con(name, 0)
      state.condef(name, Nil, typ_)
      List(smtlib.DefineSort(name, Nil, typ_))

    case VarDef(Formal(typ, name), _) =>
      val typ_ = resolve(typ)
      val x = state.global(name, typ_)
      vars = vars + (name -> x)
      List(smtlib.DeclareVar(name, typ_))

    case FunDecl(ret, "abort", formals)                => Nil
    case FunDecl(ret, "__assert_fail", formals)        => Nil
    case FunDecl(ret, "__assert_perror_fail", formals) => Nil
    case FunDecl(ret, "__assert", formals)             => Nil
    case FunDecl(ret, "__VERIFIER_error", formals)     => Nil
    case FunDecl(ret, "__VERIFIER_assume", formals)    => Nil

    case FunDecl(ret, name, formals) if name startsWith "__VERIFIER_nondet" =>
      funs += (name -> (formals, ret))
      Nil

    case FunDef(ret, "reach_error", formals, body)         => Nil
    case FunDef(ret, "__VERIFIER_assert", formals, body)   => Nil
    case FunDef(ret, "assume_abort_if_not", formals, body) => Nil

    case FunDecl(ret, name, formals) =>
      funs += (name -> (formals, ret))

      val in_ = vars(formals)
      val out_ = List(result(ret))
      val mod_ = vars.values filterNot in_.contains
      val spec_ = imp.Spec( /*heap :: */ mod_.toList, pure.True, pure.True)

      if (state.procs contains name) {
        Nil
      } else {
        state.proc(name, Nil, in_, out_, None)
        List(smtlib.DeclareProc(name, Nil, in_, out_, Some(spec_)))
      }

    case FunDef(ret, name, formals, body) =>
      funs += (name -> (formals, ret))

      val in_ = vars(formals)
      val ret_ = result(ret)
      val out_ = List(ret_)
      val scope = vars ++ Map(in_.asSimpleScope: _*)
      val mod_ = vars.values filterNot in_.contains
      val spec_ = imp.Spec( /* heap :: */ mod_.toList, pure.True, pure.True)

      val prelude = if (name == "main") {
        init(all, scope)
      } else {
        Nil
      }

      val progs = locals(List(body), scope, Nil, ret_)

      val body_ = block(prelude ++ progs)

      state.proc(name, Nil, in_, out_, None)
      state.procdef(name, in_, out_, body_)
      List(smtlib.DefineProc(name, Nil, in_, out_, Some(spec_), body_))

    case Group(stmts) =>
      globals(stmts)

    case stmt =>
      cuvee.error("unsupported global declaration: " + stmt)

    // case StructDecl(name) =>
    //   ???

    // case UnionDecl(name) =>
    //   ???

    // case EnumDecl(name) =>
    //   ???

    // case StructDef(name, fields) =>
    //   ???

    // case UnionDef(name, fields) =>
    //   ???

    // case EnumDef(name, consts) =>
    //   ???
  }

  def unblock(
      progs: List[imp.Prog],
      scope: Map[String, pure.Var]
  ): List[imp.Prog] =
    progs match {
      case Nil =>
        Nil
      case List(block: imp.Block) =>
        progs
      case _ if progs.local disjoint scope.values.toSet =>
        progs
      case _ =>
        List(imp.Block(progs))
    }

  def cleanup(progs: List[imp.Prog]): List[imp.Prog] =
    progs match {
      case Nil =>
        Nil

      case (prog @ imp.Local(List(x), List(a))) :: rest =>
        if (rest.vars contains x)
          prog :: cleanup(rest)
        else
          cleanup(rest)

      case prog :: rest =>
        prog :: cleanup(rest)
    }
  def block(progs: List[imp.Prog]): imp.Prog =
    progs match {
      case List(imp.Block(inner)) =>
        block(inner)
      case _ =>
        imp.Block(cleanup(progs))
    }

  def locals(
      stmts: List[Stmt],
      scope: Map[String, pure.Var],
      cont: List[(List[Stmt], Map[String, pure.Var])],
      result: pure.Var
  ): List[imp.Prog] =
    stmts match {
      case Nil =>
        cont match {
          case Nil =>
            Nil
          case (stmts, scope) :: cont =>
            locals(stmts, scope, cont, result)
        }

      case Atomic(None) :: rest =>
        locals(rest, scope, cont, result)

      case Atomic(Some(BinOp("=", Id(lhs), FunCall(name, args)))) :: rest
          if name startsWith "__VERIFIER_nondet" =>
        val (formals, ret) = funs(name)
        val x = scope(lhs)
        val havoc_ = imp.Spec.havoc(List(x))

        if (!Translate.assumeBounds) {
          List(havoc_) ++ locals(rest, scope, cont, result)
        } else {
          val bounds_ = imp.Spec.assume(bounds(x, ret))
          List(havoc_, bounds_) ++ locals(rest, scope, cont, result)
        }

      case (stmt @ VarDef(Formal(typ, lhs), Some(FunCall(name, args)))) :: rest
          if name startsWith "__VERIFIER_nondet" =>
        val (formals, ret) = funs(name)
        val typ_ = resolve(typ)
        val x = pure.Var(lhs, typ_)
        val havoc_ = imp.Local(List(x), List())

        if (!Translate.assumeBounds) {
          List(havoc_) ++ locals(rest, scope + (lhs -> x), cont, result)
        } else {
          val bounds_ = imp.Spec.assume(bounds(x, ret))
          List(havoc_, bounds_) ++ locals(rest, scope + (lhs -> x), cont, result)
        }

      case Atomic(Some(expr)) :: rest =>
        val (_, progs) = eval(expr, scope)
        progs ++ locals(rest, scope, cont, result)

      // artificial, e.g., from multiple initialized vars
      case Group(stmts) :: rest =>
        locals(stmts ++ rest, scope, cont, result)

      case Block(Nil) :: rest =>
        locals(rest, scope, cont, result)

      case Block(List(block: Block)) :: rest =>
        locals(block :: rest, scope, cont, result)

      case Block(stmts) :: rest =>
        val progs = locals(stmts, scope, cont, result)
        val prefix = unblock(progs, scope)
        prefix ++ locals(rest, scope, cont, result)

      case Continue :: rest =>
        List(imp.Continue) // ignores rest!

      case Break :: rest =>
        List(imp.Break) // ignores rest!

      case Return(None) :: rest =>
        List(imp.Return) // ignores rest!

      case Return(Some(expr)) :: rest =>
        val (expr_, progs) = eval(expr, scope)
        val asg_ = imp.Assign(List(result), List(expr_))
        val ret_ = imp.Return
        progs ++ List(asg_, ret_) // ignores rest!

      case (stmt @ VarDef(Formal(typ, name), None)) :: rest =>
        val typ_ = resolve(typ)
        val x = pure.Var(name, typ_)
        val local_ = imp.Local(List(x), Nil)
        val scope_ = scope + (name -> x)
        List(local_) ++ locals(rest, scope_, cont, result)

      // XXX: pattern used in sv-benchmarks to initialize arrays
      case (stmt @ VarDef(
            Formal(PtrType(typ), name),
            Some(FunCall("malloc", List(BinOp("*", SizeOfType(typ_), n))))
          )) :: rest =>
        val typ_ = pure.Sort.array(pure.Sort.int, resolve(typ))
        val x = pure.Var(name, typ_)
        val local_ = imp.Local(List(x), Nil)
        val scope_ = scope + (name -> x)
        List(local_) ++ locals(rest, scope_, cont, result)

      case (stmt @ VarDef(Formal(typ, name), Some(init))) :: rest =>
        val typ_ = resolve(typ)
        val x = pure.Var(name, typ_)
        val (init_, progs) = eval(init, scope)

        // Note, in C variable initialization refers to itself, but locals in Boogie don't
        val isSimple = progs.isEmpty && !(x in init_)
        val rest_ = locals(rest, scope + (name -> x), cont, result)

        if (isSimple) {
          val local_ = imp.Local(List(x), List(init_))
          List(local_) ++ rest_
        } else {
          val local_ = imp.Local(List(x), Nil)
          val asg_ = imp.Assign(List(x), List(init_))
          progs ++ List(local_, asg_) ++ rest_
        }

      case If(test, left, right) :: rest =>
        val (test_, progs) = eval(test, scope)
        val left_ = locals(List(left), scope, cont, result)
        val right_ = locals(List(right), scope, cont, result)
        val if_ = imp.If(truth(test_), block(left_), block(right_))
        progs ++ List(if_) ++ locals(rest, scope, cont, result)

      case While(test, body) :: rest =>
        val (test_, progs) = eval(test, scope)
        val body_ = locals(List(body), scope, cont, result)
        if (progs.isEmpty) {
          val while_ = imp.While(truth(test_), block(body_))
          List(while_) ++ locals(rest, scope, cont, result)
        } else {
          val exit_ = imp.If(!truth(test_), imp.Break)
          val while_ = imp.While(pure.True, block(List(exit_) ++ body_))
          progs ++ List(while_) ++ locals(rest, scope, cont, result)
        }

      case DoWhile(body, test) :: rest =>
        val (test_, progs) = eval(test, scope)
        val body_ = locals(List(body), scope, cont, result)
        val exit_ = imp.If(!truth(test_), imp.Break)
        val while_ = imp.While(pure.True, block(body_ ++ List(exit_)))
        progs ++ List(while_) ++ locals(rest, scope, cont, result)

      case For(vars, init, test, inc, body) :: rest =>
        val init_ = Expr.comma(init)
        val test_ = Expr.comma(test) getOrElse Lit(1)
        val inc_ = Expr.comma(inc)
        val body_ = Block(List(body, Atomic(inc_)))
        val loop_ = While(test_, body_)
        val stmt_ = Block(List(Group(vars), Atomic(init_), loop_))
        locals(stmt_ :: rest, scope, cont, result)

      case Label(label, stmt) :: rest =>
        locals(stmt :: rest, scope, cont, result)

      case stmt :: _ =>
        cuvee.error("unsupported statement: " + stmt)

      // case Case(const, stmt) :: rest =>
      //   ???

      // case Switch(expr, body) :: rest =>
      //   ???

      // case Goto(label) :: rest =>
      //   ???
    }

  def truth(arg: pure.Expr): pure.Expr = {
    arg match {
      case pure.Ite(test, pure.One, pure.Zero) =>
        test
      case pure.Ite(test, pure.Zero, pure.One) =>
        !test
      case _ =>
        arg !== pure.Zero
    }
  }

  def bool(arg: pure.Expr): pure.Expr = {
    arg match {
      case pure.Not(arg) =>
        pure.Ite(arg, pure.Zero, pure.One)
      case _ =>
        pure.Ite(arg, pure.One, pure.Zero)
    }
  }

  def assign(
      lhs: Expr,
      rhs_ : pure.Expr,
      scope: Map[String, pure.Var]
  ): (pure.Expr, List[imp.Prog]) =
    lhs match {
      case Id(name) =>
        val x = scope(name)

        x.typ match {
          case pure.Sort(pure.Con.array, args) =>
            cuvee.error(
              "asliasing in array assignments not supported for: " + x + " = " + rhs_
            )
          case _ =>
        }

        val asg_ = imp.Assign(List(x), List(rhs_))
        (x, List(asg_))

      case Index(Id(name), index1) =>
        val (index1_, progs1) = eval(index1, scope)
        val x = scope(name)
        val lhs_ = pure.Select(x, index1_)
        val asg_ = imp.Assign.from(lhs_, rhs_)
        (x, progs1 ++ List(asg_))

      case Index(Index(Id(name), index1), index2) =>
        val (index1_, progs1) = eval(index1, scope)
        val (index2_, progs2) = eval(index2, scope)
        val x = scope(name)
        val lhs_ = pure.Select(pure.Select(x, index1_), index2_)
        val asg_ = imp.Assign.from(lhs_, rhs_)
        (x, progs1 ++ progs2 ++ List(asg_))

      case Index(Index(Index(Id(name), index1), index2), index3) =>
        val (index1_, progs1) = eval(index1, scope)
        val (index2_, progs2) = eval(index2, scope)
        val (index3_, progs3) = eval(index3, scope)
        val x = scope(name)
        val lhs_ = pure.Select(pure.Select(pure.Select(x, index1_), index2_), index3_)
        val asg_ = imp.Assign.from(lhs_, rhs_)
        (x, progs1 ++ progs2 ++ progs3 ++ List(asg_))

      case Index(Index(Index(Index(Id(name), index1), index2), index3), index4) =>
        val (index1_, progs1) = eval(index1, scope)
        val (index2_, progs2) = eval(index2, scope)
        val (index3_, progs3) = eval(index3, scope)
        val (index4_, progs4) = eval(index4, scope)
        val x = scope(name)
        val lhs_ =
          pure.Select(pure.Select(pure.Select(pure.Select(x, index1_), index2_), index3_), index4_)
        val asg_ = imp.Assign.from(lhs_, rhs_)
        (x, progs1 ++ progs2 ++ progs3 ++ progs4 ++ List(asg_))
    }

  def evals(
      exprs: List[Expr],
      scope: Map[String, pure.Var]
  ): (List[pure.Expr], List[imp.Prog]) =
    exprs match {
      case Nil =>
        (Nil, Nil)
      case expr :: rest =>
        val (expr_, progs1) = eval(expr, scope)
        val (rest_, progs2) = evals(rest, scope)
        (expr_ :: rest_, progs1 ++ progs2)
    }

  def eval(
      expr: Expr,
      scope: Map[String, pure.Var]
  ): (pure.Expr, List[imp.Prog]) =
    expr match {
      case Lit(arg: java.lang.Long) =>
        (pure.Lit(BigInt(arg), pure.Sort.int), Nil)

      case Lit(arg: java.lang.Double) =>
        (pure.Lit(arg, pure.Sort.real), Nil)

      case Lit(arg: java.lang.String) =>
        (pure.Lit(arg, pure.Sort.string), Nil)

      case Id(name) =>
        require(
          scope contains name,
          "name unbound: " + name + " in " + scope.values.mkString(", ")
        )
        (scope(name), Nil)

      case PreOp("~", arg) =>
        ???

      case PreOp("*", arg) =>
        ???
      case PreOp("&", arg) =>
        ???

      case PreOp("++", arg) =>
        val (arg_, progs1) = eval(arg, scope)
        val (res, progs2) = assign(arg, arg_ + pure.One, scope)
        (res, progs1 ++ progs2)

      case PreOp("--", arg) =>
        val (arg_, progs1) = eval(arg, scope)
        val (res, progs2) = assign(arg, arg_ - pure.One, scope)
        (res, progs1 ++ progs2)

      case PostOp("++", arg) =>
        val (arg_, progs1) = eval(arg, scope)
        val x0 = pure.Expr.fresh("x", arg_.typ)
        val asg_ = imp.Local(List(x0), List(arg_))
        val (res, progs2) = assign(arg, arg_ + pure.One, scope)
        (x0, progs1 ++ List(asg_) ++ progs2)

      case PostOp("--", arg) =>
        val (arg_, progs1) = eval(arg, scope)
        val x0 = pure.Expr.fresh("x", arg_.typ)
        val asg_ = imp.Local(List(x0), List(arg_))
        val (res, progs2) = assign(arg, arg_ - pure.One, scope)
        (x0, progs1 ++ List(asg_) ++ progs2)

      case BinOp("=", lhs, arg) =>
        val (arg_, progs1) = eval(arg, scope)
        val (res_, progs2) = assign(lhs, arg_, scope)
        (res_, progs1 ++ progs2)

      case BinOp("&&", arg1, arg2)
          if Translate.split || Expr.hasEffects(arg1) || Expr.hasEffects(arg2) =>
        val (arg1_, progs1) = eval(arg1, scope)
        val (arg2_, progs2) = eval(arg2, scope)
        val x0 = pure.Expr.fresh("x", pure.Sort.bool)
        val asg1_ = imp.Local(List(x0), List(truth(arg1_)))
        val asg2_ = imp.Assign(List(x0), List(truth(arg2_)))
        val if_ = imp.If(x0, block(progs2 ++ List(asg2_)))
        (bool(x0), progs1 ++ List(asg1_, if_))

      case BinOp("||", arg1, arg2)
          if Translate.split || Expr.hasEffects(arg1) || Expr.hasEffects(arg2) =>
        val (arg1_, progs1) = eval(arg1, scope)
        val (arg2_, progs2) = eval(arg2, scope)
        val x0 = pure.Expr.fresh("x", pure.Sort.bool)
        val asg1_ = imp.Local(List(x0), List(truth(arg1_)))
        val asg2_ = imp.Assign(List(x0), List(truth(arg2_)))
        val if_ = imp.If(!x0, block(progs2 ++ List(asg2_)))
        (bool(x0), progs1 ++ List(asg1_, if_))

      case Question(test, arg1, arg2) =>
        val (test_, progs0) = eval(test, scope)
        val (arg1_, progs1) = eval(arg1, scope)
        val (arg2_, progs2) = eval(arg2, scope)
        require(arg1_.typ == arg2_.typ, "ill-typed ternary: " + expr)
        val x0 = pure.Expr.fresh("x", arg1_.typ)
        val asg0_ = imp.Local(List(x0), Nil)
        val asg1_ = imp.Assign(List(x0), List(arg1_))
        val asg2_ = imp.Assign(List(x0), List(arg2_))
        val if_ = imp.If(
          truth(test_),
          block(progs1 ++ List(asg1_)),
          block(progs2 ++ List(asg2_))
        )
        (x0, progs0 ++ List(asg0_, if_))

      // generic ops below:
      case PreOp(op, arg) =>
        val (arg_, progs) = eval(arg, scope)
        (preop(op, arg_), progs)

      case BinOp(op, arg1, arg2) =>
        val (arg1_, progs1) = eval(arg1, scope)
        val (arg2_, progs2) = eval(arg2, scope)
        (binop(op, arg1_, arg2_), progs1 ++ progs2)

      case Index(base, index) =>
        val (base_, progs1) = eval(base, scope)
        val (index_, progs2) = eval(index, scope)
        (pure.Select(base_, index_), progs1 ++ progs2)

      case FunCall("assume", List(arg)) =>
        val (arg_, progs) = eval(arg, scope)
        val assm_ = imp.Spec.assume(truth(arg_))
        (void, progs ++ List(assm_))

      case FunCall("assume_abort_if_not", List(arg)) =>
        val (arg_, progs) = eval(arg, scope)
        val assm_ = imp.Spec.assume(truth(arg_))
        (void, progs ++ List(assm_))

      case FunCall("reach_error", List()) =>
        if (Translate.translateAsserts)
          (void, List(imp.Spec.assert(pure.False)))
        else
          (void, Nil)

      case FunCall("assert", List(arg)) =>
        val (arg_, progs) = eval(arg, scope)
        val assrt_ = imp.Spec.assert(truth(arg_))
        if (Translate.translateAsserts)
          (void, progs ++ List(assrt_))
        else
          (void, progs) // keep side-effects

      case FunCall("__VERIFIER_assume", List(arg)) =>
        val (arg_, progs) = eval(arg, scope)
        val assm_ = imp.Spec.assume(truth(arg_))
        (void, progs ++ List(assm_))

      case FunCall("__VERIFIER_assert", List(arg)) =>
        val (arg_, progs) = eval(arg, scope)
        val assrt_ = imp.Spec.assert(truth(arg_))
        if (Translate.translateAsserts)
          (void, progs ++ List(assrt_))
        else
          (void, progs) // keep side-effects

      case FunCall("__VERIFIER_error", List()) =>
        if (Translate.translateAsserts)
          (void, List(imp.Spec.assert(pure.False)))
        else
          (void, Nil)

      case FunCall(name, args) if name startsWith "__VERIFIER_nondet" =>
        val (formals, ret) = funs(name)
        val name_ = name drop "__VERIFIER_".length

        val typ_ = pure.Sort.int
        val res_ = pure.Expr.fresh(name_, typ_)
        val asg_ = imp.Local(List(res_), Nil)

        if (!Translate.assumeBounds) {
          (res_, List(asg_))
        } else {
          val bounds_ = imp.Spec.assume(bounds(res_, ret))
          (res_, List(asg_, bounds_))
        }

      case FunCall(fun, args) =>
        val name = cuvee.util.Name(fun)
        val (args_, progs) = evals(args, scope)
        val proc = state.procs(name)
        val List(out_) = proc.out
        val res_ = pure.Expr.fresh(name, out_.typ)
        val asg_ = imp.Local(List(res_), Nil)
        val call_ = imp.Call(name, args_, List(res_))
        (res_, progs ++ List(asg_, call_))

      case SizeOfType(typ) =>
        (pure.Lit(BigInt(Type.sizeof(typ)), pure.Sort.int), Nil)

      case Cast(typ, inner) =>
        // XXX: some kind of hack
        eval(inner, scope)

      case _ =>
        cuvee.error("unsupported expression: " + expr)

      // case Dot(expr, field) =>
      //   ???
      // case SizeOfExpr(expr) =>
      //   ???
      // case Arrow(expr, field) =>
      //   ???
    }

  def preop(op: String, arg: pure.Expr) =
    op match {
      case "+" => +arg
      case "-" => -arg
      case "!" => bool(!truth(arg))
    }

  def binop(op: String, arg1: pure.Expr, arg2: pure.Expr) =
    op match {
      case "+"  => arg1 + arg2
      case "-"  => arg1 - arg2
      case "*"  => arg1 * arg2
      case "/"  => arg1 / arg2
      case "%"  => arg1 % arg2
      case "&"  => bitand(arg1, arg2)
      case "^"  => bitxor(arg1, arg2)
      case "|"  => bitor(arg1, arg2)
      case "<"  => bool(arg1 < arg2)
      case "<=" => bool(arg1 <= arg2)
      case ">=" => bool(arg2 <= arg1)
      case ">"  => bool(arg2 < arg1)
      case "==" => bool(arg1 === arg2)
      case "!=" => bool(arg1 !== arg2)
      case "&&" => bool(truth(arg1) && truth(arg2))
      case "||" => bool(truth(arg1) || truth(arg2))
    }

  def vars(formals: List[Formal]) =
    for (Formal(typ, name) <- formals)
      yield pure.Var(name, resolve(typ))

  def resolves(types: List[Type]) =
    for (typ <- types)
      yield resolve(typ)

  def resolve(typ: Type): pure.Type = typ match {
    case PtrType(typ) =>
      ptr(typ)

    case FunPtrType(ret, args) =>
      // not supported (arrays don't fit because C functions can have side-effects)
      ???

    case Type._Bool =>
      pure.Sort.bool

    case Type._float =>
      pure.Sort.real

    case Type._double =>
      pure.Sort.real

    case Type._void =>
      Void

    case Unsigned(name, bytes) =>
      pure.Sort.int

    case Signed(name, bytes) =>
      pure.Sort.int

    case ArrayType(typ, dim) =>
      val typ_ = resolve(typ)
      pure.Sort.array(pure.Sort.int, typ_)

    case TypedefName(name) =>
      state.sort(name)

    case _ =>
      cuvee.error("unsupported type: " + typ)

    // case EnumName(name) =>
    //   ???

    // case StructName(name) =>
    //   ???

    // case UnionName(name) =>
    //   ???

    // case AnonEnum(consts) =>
    //   ???

    // case AnonStruct(fields) =>
    //   ???

    // case AnonUnion(fields) =>
    //   ???
  }
}

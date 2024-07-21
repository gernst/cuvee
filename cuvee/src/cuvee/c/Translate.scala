package cuvee.c

import cuvee.State
import cuvee.pure
import cuvee.imp
import cuvee.smtlib
import scala.collection.immutable

object Translate {
  val (prelude, state) = cuvee.boogie.parse("cuvee/src/cuvee/c/c.bpl")
}

class Translate(state: State) {
  val heap = state.vars("c#heap")

  def ptr(typ: Type) =
    state.sort("c#ptr", List(resolve(typ)))

  def result(typ: Type) =
    pure.Var("c#result", resolve(typ))

  var vars: Map[String, pure.Var] = Map()

  def globals(stmts: List[Stmt]): List[smtlib.Cmd] =
    for (
      stmt <- stmts;
      prog <- global(stmt)
    )
      yield prog

  def global(stmt: Stmt): List[smtlib.Cmd] = stmt match {
    case StructDecl(name) =>
      ???

    case UnionDecl(name) =>
      ???

    case EnumDecl(name) =>
      ???

    case StructDef(name, fields) =>
      ???

    case UnionDef(name, fields) =>
      ???

    case EnumDef(name, consts) =>
      ???

    case TypeDef(typ, name) =>
      val typ_ = resolve(typ)
      state.con(name, 0)
      state.condef(name, Nil, typ_)
      List(smtlib.DefineSort(name, Nil, typ_))

    case VarDef(Formal(typ, name), None) =>
      val typ_ = resolve(typ)
      val x = state.global(name, typ_)
      vars = vars + (name -> x)
      List(smtlib.DeclareVar(name, typ_))

    case FunDecl(ret, name, formals) =>
      val in_ = vars(formals)
      val out_ = List(result(ret))
      val mod_ = vars.values filterNot in_.contains
      val spec_ = imp.Spec(mod_.toList, pure.True, pure.True)

      state.proc(name, Nil, in_, out_, None)
      List(smtlib.DeclareProc(name, Nil, in_, out_, Some(spec_)))

    case FunDef(ret, name, formals, body) =>
      val in_ = vars(formals)
      val ret_ = result(ret)
      val out_ = List(ret_)
      val scope = vars ++ Map(in_.asSimpleScope: _*)
      val mod_ = vars.values filterNot in_.contains
      val spec_ = imp.Spec(mod_.toList, pure.True, pure.True)
      val body_ = imp.Block(locals(List(body), scope, Nil, ret_))

      state.proc(name, Nil, in_, out_, None)
      state.procdef(name, in_, out_, body_)
      List(smtlib.DefineProc(name, Nil, in_, out_, Some(spec_), body_))

    // global blocks are artificial, don't nest
    case Block(stmts) =>
      globals(stmts)
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

      case Atomic(Some(expr)) :: rest =>
        val (_, progs) = eval(expr, scope)
        progs ++ locals(rest, scope, cont, result)

      case Block(stmts) :: rest =>
        val progs = locals(stmts, scope, cont, result)
        List(imp.Block(progs)) ++ locals(rest, scope, cont, result)

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

      case VarDef(Formal(typ, name), None) :: rest =>
        val typ_ = resolve(typ)
        val x = pure.Var(name, typ_)
        val local_ = imp.Local(List(x), Nil)
        List(local_) ++ locals(rest, scope + (name -> x), cont, result)

      case VarDef(Formal(typ, name), Some(init)) :: rest =>
        val typ_ = resolve(typ)
        val x = pure.Var(name, typ_)
        val (init_, progs) = eval(init, scope)
        // Note, in C variable initialization refers to itself, but locals in Boogie don't
        val local_ = imp.Local(List(x), Nil)
        val asg_ = imp.Assign(List(x), List(init_))
        progs ++ List(local_, asg_) ++ locals(rest, scope + (name -> x), cont, result)

      case If(test, left, right) :: rest =>
        val (test_, progs) = eval(test, scope)
        val left_ = locals(List(left), scope, cont, result)
        val right_ = locals(List(right), scope, cont, result)
        val if_ = imp.If(truth(test_), imp.Block(left_), imp.Block(right_))
        progs ++ List(if_) ++ locals(rest, scope, cont, result)

      case While(test, body) :: rest =>
        val (test_, progs) = eval(test, scope)
        val body_ = locals(List(body), scope, cont, result)
        val exit_ = imp.If(!truth(test_), imp.Break)
        val while_ = imp.While(pure.True, imp.Block(List(exit_) ++ body_))
        progs ++ List(while_) ++ locals(rest, scope, cont, result)

      case DoWhile(body, test) :: rest =>
        val (test_, progs) = eval(test, scope)
        val body_ = locals(List(body), scope, cont, result)
        val exit_ = imp.If(!truth(test_), imp.Break)
        val while_ = imp.While(pure.True, imp.Block(body_ ++ List(exit_)))
        progs ++ List(while_) ++ locals(rest, scope, cont, result)

      case For(vars, init, test, inc, body) :: rest =>
        val init_ = Expr.comma(init)
        val test_ = Expr.comma(test) getOrElse Lit(1)
        val inc_ = Expr.comma(inc)
        val body_ = Block(List(body, Atomic(inc_)))
        val loop_ = While(test_, body_)
        val stmt_ = Block(List(Block(vars), Atomic(init_), loop_))
        locals(stmt_ :: rest, scope, cont, result)

      case Label(label, stmt) :: rest =>
        ???

      case Case(const, stmt) :: rest =>
        ???

      case Switch(expr, body) :: rest =>
        ???

      case Goto(label) :: rest =>
        ???
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

  def eval(expr: Expr, scope: Map[String, pure.Var]): (pure.Expr, List[imp.Prog]) = expr match {
    case Lit(arg: java.lang.Long) =>
      (pure.Lit(BigInt(arg), pure.Sort.int), Nil)

    case Lit(arg: java.lang.Double) =>
      (pure.Lit(arg, pure.Sort.real), Nil)

    case Lit(arg: java.lang.String) =>
      (pure.Lit(arg, pure.Sort.string), Nil)

    case Id(name) =>
      (scope(name), Nil)

    case PostOp("++", arg) =>
      ???
    case PostOp("--", arg) =>
      ???

    case PreOp("~", arg) =>
      ???
    case PreOp("*", arg) =>
      ???
    case PreOp("&", arg) =>
      ???
    case PreOp("++", arg) =>
      ???
    case PreOp("--", arg) =>
      ???

    case BinOp("=", Id(name), arg2) =>
      val (arg2_, progs2) = eval(arg2, scope)
      val x = scope(name)
      val asg_ = imp.Assign(List(x), List(arg2_))
      (x, progs2 ++ List(asg_))

    // generic ops below:
    case PreOp(op, arg) =>
      val (arg_, progs) = eval(arg, scope)
      (preop(op, arg_), progs)

    case BinOp(op, arg1, arg2) =>
      val (arg1_, progs1) = eval(arg1, scope)
      val (arg2_, progs2) = eval(arg2, scope)
      (binop(op, arg1_, arg2_), progs1 ++ progs2)

    case Dot(expr, field) =>
      ???
    case FunCall(fun, args) =>
      ???
    case Index(base, index) =>
      ???
    case SizeOfExpr(expr) =>
      ???
    case Arrow(expr, field) =>
      ???
    case Question(test, left, right) =>
      ???
    case SizeOfType(typ) =>
      ???
    case Cast(typ, expr) =>
      ???
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
      case "*"  => arg1 - arg2
      case "/"  => arg1 - arg2
      case "%"  => arg1 - arg2
      case "<"  => bool(arg1 < arg2)
      case "<=" => bool(arg1 <= arg2)
      case ">=" => bool(arg2 <= arg1)
      case ">"  => bool(arg2 < arg1)
      case "==" => bool(arg1 === arg2)
      case "!=" => bool(arg1 !== arg2)
    }

  def vars(formals: List[Formal]) =
    for (Formal(typ, name) <- formals)
      yield pure.Var(name, resolve(typ))

  def resolves(types: List[Type]) =
    for (typ <- types)
      yield resolve(typ)

  def resolve(typ: Type): pure.Type = typ match {
    case AnonEnum(consts) =>
      ???
    case AnonStruct(fields) =>
      ???
    case AnonUnion(fields) =>
      ???
    case PtrType(typ) =>
      ???
    case FunPtrType(ret, args) =>
      ???
    case EnumName(name) =>
      ???
    case StructName(name) =>
      ???
    case TypedefName(name) =>
      ???
    case UnionName(name) =>
      ???
    case Unsigned(name, bytes) =>
      ???
    case Signed(name, bytes) =>
      pure.Sort.int
    case ArrayType(typ, dim) =>
      ???
    case BaseType(name) =>
      ???
  }
}

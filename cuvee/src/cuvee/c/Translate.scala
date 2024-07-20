package cuvee.c

import cuvee.State
import cuvee.pure
import cuvee.imp
import cuvee.smtlib

class Translate(state: State) {

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
      state.global(name, typ_)
      List(smtlib.DeclareVar(name, typ_))

    case FunDecl(ret, name, types) =>
      ???

    case FunDef(ret, name, formals, body) =>
      ???

    case Block(stmts) =>
      globals(stmts)
  }

  def locals(stmts: List[Stmt], result: pure.Var): List[imp.Prog] =
    for (
      stmt <- stmts;
      prog <- local(stmt, result)
    )
      yield prog

  def local(stmt: Stmt, result: pure.Var): List[imp.Prog] = stmt match {
    case Atomic(None) =>
      Nil

    case Atomic(Some(expr)) =>
      val (_, progs) = eval(expr)
      progs

    case Block(stmts) =>
      locals(stmts, result)

    case Continue =>
      List(imp.Continue)

    case Break =>
      List(imp.Break)

    case Return(None) =>
      List(imp.Return)

    case Return(Some(expr)) =>
      val (expr_, progs) = eval(expr)
      val asg_ = imp.Assign(List(result), List(expr_))
      val ret_ = imp.Return
      progs ++ List(asg_, ret_)

    case VarDef(Formal(typ, name), None) =>
      val typ_ = resolve(typ)
      val x = pure.Var(name, typ_)
      val local_ = imp.Local(List(x), Nil)
      List(local_)

    case VarDef(Formal(typ, name), Some(init)) =>
      val typ_ = resolve(typ)
      val x = pure.Var(name, typ_)
      val (init_, progs) = eval(init)
      // Note, in C variable initialization refers to itself, but locals in Boogie don't
      val local_ = imp.Local(List(x), Nil)
      val asg_ = imp.Assign(List(x), List(init_))
      progs ++ List(local_, asg_)

    case Block(stmts) =>
      val progs = locals(stmts, result)
      List(imp.Block(progs))

    case If(test, left, right) =>
      val (test_, progs) = eval(test)
      val left_ = local(left, result)
      val right_ = local(right, result)
      val if_ = imp.If(test_, imp.Block(left_), imp.Block(right_))
      progs ++ List(if_)

    case While(test, body) =>
      val (test_, progs) = eval(test)
      val body_ = local(body, result)
      val exit_ = imp.If(!test_, imp.Break)
      val while_ = imp.While(pure.True, imp.Block(List(exit_) ++ body_))
      progs ++ List(while_)

    case DoWhile(body, test) =>
      val (test_, progs) = eval(test)
      val body_ = local(body, result)
      val exit_ = imp.If(!test_, imp.Break)
      val while_ = imp.While(pure.True, imp.Block(body_ ++ List(exit_)))
      progs ++ List(while_)

    case For(vars, init, test, inc, body) =>
      val init_ = Expr.comma(init)
      val test_ = Expr.comma(test) getOrElse Lit(1)
      val inc_ = Expr.comma(inc)
      val body_ = Block(List(body, Atomic(inc_)))
      val loop_ = While(test_, body_)
      val stmt_ = Block(List(Block(vars), Atomic(init_), loop_))
      local(stmt_, result)

    case Label(label, stmt) =>
      ???

    case Case(const, stmt) =>
      ???

    case Switch(expr, body) =>
      ???

    case Goto(label) =>
      ???
  }

  def eval(expr: Expr): (pure.Expr, List[imp.Prog]) = {
    ???
  }

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

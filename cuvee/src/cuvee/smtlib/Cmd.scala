package cuvee.smtlib

import cuvee.pure._

import cuvee.boogie
import cuvee.sexpr
import scala.reflect.ClassTag
import cuvee.backend.Tactic
import cuvee.imp.Prog
import cuvee.util.Name

sealed trait Res
sealed trait IsSat extends Res
sealed trait Ack extends Res

case object Success extends Ack
case object Unsupported extends Ack
case class Error(info: List[Any]) extends Ack with IsSat

case object Sat extends IsSat
case object Unknown extends IsSat
case object Unsat extends IsSat

case class Assertions(exprs: List[Expr]) extends Res
case class Model(defs: List[DefineFun]) extends Res

sealed trait Cmd extends sexpr.Syntax with boogie.Syntax
sealed trait Decl extends Cmd
sealed trait Ctrl extends Cmd

case object Labels extends Cmd {
  def sexpr = List("labels")
  def bexpr = ???
}

case class SetLogic(logic: String) extends Ctrl {
  def sexpr = List("set-logic", logic)
  def bexpr =
    List("/* ", "Command unsupported in boogie:", "set-logic", logic, " */")
}

case class SetOption(attr: String, arg: Any) extends Ctrl {
  def sexpr = List("set-option", ":" + attr, arg)
  def bexpr = List(
    "/* ",
    "Command unsupported in boogie:",
    "set-option",
    attr,
    arg,
    " */"
  )
}

case class GetInfo(attr: String) extends Ctrl {
  def sexpr = List("get-info", ":" + attr)
  def bexpr =
    List("/* ", "Command unsupported in boogie:", "get-info", attr, " */")
}

case class SetInfo(attr: String, arg: Option[Any]) extends Ctrl {
  def sexpr = arg match {
    case None      => List("set-info", ":" + attr)
    case Some(arg) => List("set-info", ":" + attr, arg)
  }


  def bexpr =
    List("/* ", "Command unsupported in boogie:", "set-info", attr, " */")
}

case class Push(depth: Int) extends Ctrl {
  def sexpr = List("push", depth)
  def bexpr = ???
}

case class Pop(depth: Int) extends Ctrl {
  def sexpr = List("pop", depth)
  def bexpr = ???
}

case object GetAssertions extends Cmd {
  def sexpr = List("get-assertions")
  def bexpr = ???
}
case object GetModel extends Cmd {
  def sexpr = List("get-model")
  def bexpr = ???
}
case object Exit extends Ctrl {
  def sexpr = List("exit")
  def bexpr = ???
}
case object Reset extends Ctrl {
  def sexpr = List("reset")
  def bexpr = ???
}

case class Assert(expr: Expr) extends Cmd {
  def sexpr = List("assert", expr)
  def bexpr = List("assert", " ", expr, ";")
}

// This is not actually a feature of SMTLIB's
case class Lemma(expr: Expr, tactic: Option[Tactic]) extends Cmd {
  def sexpr = List("lemma", expr)
  def bexpr = tactic match {
    case None         => List("lemma", expr, ";")
    case Some(tactic) => List("lemma", expr, "proof", tactic, ";")
  }
}

case object CheckSat extends Cmd {
  def sexpr = List("check-sat")
  def bexpr = ???
}

case class DeclareSort(name: Name, arity: Int) extends Decl {
  def sexpr = List("declare-sort", name, arity)
  def bexpr = List("type", " ", name, ";")
}
case class DefineSort(name: Name, args: List[Param], body: Type) extends Decl {
  def sexpr = List("define-sort", name, args, body)
  def bexpr = ??? // TODO: Is this right?
}

case class DeclareFun(name: Name, args: List[Type], res: Type) extends Decl {
  def sexpr = List("declare-fun", name, args, res)
  def bexpr = List("function", " ", name, "(", args, ")", ":", res)
}

case class DefineFun(
    name: Name,
    formals: List[Var],
    res: Type,
    body: Expr,
    rec: Boolean
) extends Decl {
  def sexpr = List(
    if (rec) "define-fun-rec" else "define-fun",
    name,
    formals.asFormals,
    res,
    body
  )
  def bexpr = List(
    "function",
    " ",
    name,
    "(",
    formals.asFormals,
    ")",
    ":",
    " ",
    res,
    "\n",
    "{ ",
    body,
    " }",
    "\n"
  )
}

case class DeclareDatatypes(arities: List[(Name, Int)], cmds: List[Datatype])
    extends Decl {
  def sexpr = List("declare-datatypes", arities, cmds)
  def bexpr = List(
    "/* ",
    "declare-datatypes",
    " arities: ",
    arities,
    ", commands: ",
    cmds,
    "*/"
  ) // What should we do here?
}

case class DeclareProc(
    name: Name,
    in: List[Type],
    out: List[Type]
) extends Decl {
  def sexpr = ???
  def bexpr = ???
}

case class DefineProc(
    name: Name,
    in: List[Var],
    out: List[Var],
    body: Prog
) extends Decl {
  def sexpr = ???
  def bexpr = ???
}

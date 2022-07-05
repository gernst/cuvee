package cuvee.smtlib

import cuvee.pure._

import cuvee.sexpr
import scala.reflect.ClassTag
import cuvee.backend.Tactic

sealed trait Res
sealed trait IsSat extends Res
sealed trait Ack extends Res

case object Success extends Ack
case object Unsupported extends Ack
case class Error(info: Seq[Any]) extends Res

case object Sat extends IsSat
case object Unknown extends IsSat
case object Unsat extends IsSat

case class Assertions(exprs: List[Expr]) extends Res
case class Model(defs: List[DefineFun]) extends Res

sealed trait Cmd extends sexpr.Syntax
sealed trait Decl extends Cmd
sealed trait Ctrl extends Cmd

case class SetLogic(logic: String) extends Ctrl {
  def sexpr = List("set-logic", logic)
}

case class SetOption(args: List[String]) extends Ctrl {
  def sexpr = "set-option" :: args
}

case class SetInfo(attr: String, arg: Option[Any]) extends Ctrl {
  def sexpr = ??? // List("set-info")
}

case class Push(depth: Int) extends Ctrl {
  def sexpr = List("push", depth)
}

case class Pop(depth: Int) extends Ctrl {
  def sexpr = List("pop", depth)
}

case object GetAssertions extends Cmd {
  def sexpr = List("get-assertions")
}
case object GetModel extends Cmd {
  def sexpr = List("get-model")
}
case object Exit extends Ctrl {
  def sexpr = List("exit")
}
case object Reset extends Ctrl {
  def sexpr = List("reset")
}

case class Assert(expr: Expr) extends Cmd {
  def sexpr = List("assert", expr)
}

case object CheckSat extends Cmd {
  def sexpr = List("check-sat")
}

case class DeclareSort(name: Name, arity: Int) extends Decl {
  def sexpr = List("declare-sort", name, arity)
}
case class DefineSort(name: Name, args: List[Param], body: Type) extends Decl {
  def sexpr = List("define-sort", name, args, body)
}

case class DeclareFun(name: Name, args: List[Type], res: Type) extends Decl {
  def sexpr = List("declare-fun", name, args, res)
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
}

case class DeclareDatatypes(arities: List[(Name, Int)], cmds: List[Datatype])
    extends Decl {
  def sexpr = List("declare-datatypes", arities, cmds)
}

// This is not actually a feature of SMTLIB's
case class Lemma(expr: Expr, tactic: Option[Tactic]) extends Cmd {
  def sexpr = ???
}
package cuvee.smtlib

import cuvee.pure._

import cuvee.sexpr

sealed trait Cmd extends sexpr.Syntax

case class SetLogic(logic: String) extends Cmd {
  def sexpr = List("set-logic", logic)
}

case class SetOption(args: List[String]) extends Cmd {
  def sexpr = "set-option" :: args
}

case class SetInfo(attr: String, arg: Option[Any]) extends Cmd {
  def sexpr = ??? // List("set-info")
}

case class Push(depth: Int) extends Cmd {
  def sexpr = List("push", depth)
}

case class Pop(depth: Int) extends Cmd {
  def sexpr = List("pop", depth)
}

case object GetAssertions extends Cmd {
  def sexpr = List("get-assertions")
}
case object GetModel extends Cmd {
  def sexpr = List("get-model")
}
case object Exit extends Cmd {
  def sexpr = List("exit")
}
case object Reset extends Cmd {
  def sexpr = List("reset")
}

case class Assert(expr: Expr) extends Cmd {
  def sexpr = List("assert", expr)
}
case class CheckSat(st: State) extends Cmd {
  def sexpr = List("check-sat")
}

case class DeclareSort(name: String, arity: Int) extends Cmd {
  def sexpr = List("declare-sort", name, arity)
}
case class DefineSort(name: String, args: List[Param], body: Type) extends Cmd {
  def sexpr = List("define-sort", name, args, body)
}

case class DeclareFun(name: String, args: List[Type], res: Type) extends Cmd {
  def sexpr = List("declare-fun", name, args, res)
}

case class DefineFun(
    name: String,
    formals: List[Var],
    res: Type,
    body: Expr,
    rec: Boolean
) extends Cmd {
  def sexpr = List(
    if (rec) "define-fun-rec" else "define-fun",
    formals.asFormals,
    res,
    body
  )
}

case class DeclareDatatypes(arities: List[(String, Int)], cmds: List[Datatype])
    extends Cmd {
  def sexpr = List("declare-datatypes", arities, cmds)
}

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

package cuvee.smtlib

import cuvee.pure._

sealed trait Cmd

case class SetLogic(logic: String) extends Cmd
case class SetOption(args: List[String]) extends Cmd
case class SetInfo(attr: String, arg: Option[Any]) extends Cmd
case class Push(depth: Int) extends Cmd
case class Pop(depth: Int) extends Cmd

case object GetAssertions extends Cmd
case object GetModel extends Cmd
case object Exit extends Cmd
case object Reset extends Cmd

case class Assert(expr: Expr) extends Cmd
case class CheckSat(st: State) extends Cmd

case class DeclareSort(name: String, arity: Int) extends Cmd
case class DefineSort(name: String, args: List[Param], body: Type) extends Cmd

case class DeclareFun(name: String, args: List[Type], res: Type) extends Cmd
case class DefineFun(
    name: String,
    formals: List[Var],
    res: Type,
    body: Expr,
    rec: Boolean
) extends Cmd

case class DeclareDatatypes(arities: List[(String, Int)], cmds: List[Datatype])
    extends Cmd

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

package cuvee.smtlib

import cuvee.pure._

import cuvee.boogie
import cuvee.sexpr
import scala.reflect.ClassTag

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

sealed trait Cmd extends sexpr.Syntax with boogie.Syntax
sealed trait Decl extends Cmd
sealed trait Ctrl extends Cmd

case class SetLogic(logic: String) extends Ctrl {
  def sexpr = List("set-logic", logic)
  def bexpr = List("/* ", "Command unsupported in boogie:", "set-logic", logic, " */")
}

case class SetOption(args: List[String]) extends Ctrl {
  def sexpr = "set-option" :: args
  def bexpr = List("/* ", "Command unsupported in boogie:", "set-logic", args.mkString(", "), " */")
}

case class SetInfo(attr: String, arg: Option[Any]) extends Ctrl {
  def sexpr = ??? // List("set-info")
  def bexpr = List("/* ", "Command unsupported in boogie:", "set-logic", arg.toString, " */")
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
    "function", " ", name,"(",
    formals.asFormals,
    ")", ":", " ", res, "\n",
    "{ ", body, " }",     "\n"
  )
}

case class DeclareDatatypes(arities: List[(Name, Int)], cmds: List[Datatype])
    extends Decl {
  def sexpr = List("declare-datatypes", arities, cmds)
  def bexpr = List("/* ", "declare-datatypes", " arities: ", arities, ", commands: ", cmds, "*/") // What should we do here?
}


package cuvee.smtlib

import cuvee.pure._

import cuvee.boogie
import scala.reflect.ClassTag
import cuvee.prove.Tactic
import cuvee.imp.Prog
import cuvee.util.Name
import cuvee.util
import cuvee.imp.Spec

sealed trait Res extends util.Syntax {}

sealed trait IsSat extends Res
sealed trait Ack extends Res

case class Info(arg: Any) extends Res

case object Success extends Ack
case object Unsupported extends Ack

case class Error(info: List[Any]) extends Exception with Res {}

object Error extends (List[Any] => Error) {
  def apply(info: List[Any]): Nothing = {
    throw new Error(info)
  }

  def apply(message: String): Nothing = {
    apply(List(message))
  }
}

case object Sat extends IsSat
case object Unsat extends IsSat
case object Unknown extends IsSat

case class Model(defs: List[DefineFun]) extends Res {
  def rename(re: Map[Var, Var]): Model = {
    val defs_ = defs map { case DefineFun(name, params, formals, res, body, rec) =>
      val name_ = re get (Var(name, res)) map (_.name) getOrElse name
      DefineFun(name_, params, formals rename re, res, body rename re, rec)
    }
    Model(defs_)
  }

  override def toString(): String = {
    var result = defs map (d => d.name + " = " + d.body.toString)
    result.mkString("model (", ", ", ")")
  }
}

sealed trait Cmd extends util.Syntax with boogie.Syntax
sealed trait Decl extends Cmd
sealed trait Ctrl extends Cmd

case object Labels extends Cmd {
  def bexpr = cuvee.undefined
}

case class Labels(labels: List[String]) extends Res {
  def bexpr = cuvee.undefined
}

case class SetLogic(logic: String) extends Ctrl {
  def bexpr =
    List("/* ", "Command unsupported in boogie:", "set-logic", logic, " */")
}

case class SetOption(attr: String, arg: Any) extends Ctrl {
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
  def bexpr =
    List("/* ", "Command unsupported in boogie:", "get-info", attr, " */")
}

case class SetInfo(attr: String, arg: Option[Any]) extends Ctrl {
  def bexpr =
    List("/* ", "Command unsupported in boogie:", "set-info", attr, " */")
}

case class Push(depth: Int) extends Ctrl {
  def bexpr = cuvee.undefined
}

case class Pop(depth: Int) extends Ctrl {
  def bexpr = cuvee.undefined
}

case object GetModel extends Cmd {
  def bexpr = cuvee.undefined
}
case object Exit extends Ctrl {
  def bexpr = cuvee.undefined
}
case object Reset extends Ctrl {
  def bexpr = cuvee.undefined
}

case class Assert(expr: Expr) extends Cmd {
  def bexpr = expr match {
    case Bind(quant, formals, body, _) =>
      List(
        "axiom " + quant.name + formals.map(_.toStringTyped).mkString(" ", ", ", " :: "),
        expr + ";"
      )
    case _ =>
      List("axiom " + expr + ";")
  }
}

// This is part neither of SMT-LIB nor of Boogie (but we support it there).
case class Lemma(expr: Expr, tactic: Option[Tactic], assert: Boolean) extends Cmd {
  def bexpr = tactic match {
    case None         => List("lemma " + expr + ";")
    case Some(tactic) => List("lemma " + expr, "proof" + tactic + ";")
  }
}

// object Lemma extends ((Expr, Option[Tactic]) => Lemma) {
//   def apply(expr: Expr, tactic: Option[Tactic]): Lemma = {
//     Lemma(expr, tactic, true)
//   }
// }

case object CheckSat extends Cmd {
  def bexpr = cuvee.undefined
}

case class DeclareSort(name: Name, arity: Int) extends Decl {
  def bexpr = List("type " + name + ";") // XXX: add params
}

case class DefineSort(name: Name, params: List[Param], body: Type) extends Decl {
  def bexpr = List("type " + name + " = " + body + ";")
}

case class DeclareFun(
    name: Name,
    params: List[Param],
    args: List[Type],
    res: Type
) extends Decl {
  def formals = Expr.vars("x", args)
  def bexpr = List("function " + name + "(" + formals.toStringTyped + "): " + res + ";")
}

case class DefineFun(
    name: Name,
    params: List[Param],
    formals: List[Var],
    res: Type,
    body: Expr,
    rec: Boolean
) extends Decl {
  require(params.isEmpty, "generic functions are currently not supported")

  def bexpr =
    List("function " + name + "(" + formals.toStringTyped + "): " + res + "{", "  " + body, "}")
}

case class DeclareDatatypes(
    arities: List[(Name, Int)],
    datatypes: List[Datatype]
) extends Decl {
  def sorts = arities zip datatypes map { case ((name, arity), Datatype(params, constrs)) =>
    Sort(Con(name, arity), params)
  }

  def bexpr = {
    val lines = arities zip datatypes map {
      case ((name, arity), Datatype(Nil, constrs)) =>
        val cs = constrs map {
          case (constr, Nil) =>
            constr.name
          case (constr, sels) =>
            val as = sels map { case Fun(name, _, List(arg), _) =>
              name + ": " + arg
            }
            constr.name + as.mkString("(", ", ", ")")
        }
        name + cs.mkString(" = ", " | ", ";")
      case ((name, arity), Datatype(params, constrs)) =>
        val cs = constrs map {
          case (constr, Nil) =>
            constr.name
          case (constr, sels) =>
            val as = sels map { case Fun(name, _, List(arg), _) => name + ": " + arg }
            constr.name + as.mkString("(", ", ", ")")
        }
        name + params.mkString("<", ", ", ">") + cs.mkString(" = ", " | ", ";")
    }

    "data " :: lines
  }
}

case class DeclareProc(
    name: Name,
    params: List[Param],
    in: List[Var],
    out: List[Var],
    spec: Option[Spec]
) extends Decl {
  def sexpr = (params, spec) match {
    case (Nil, None) =>
      List("declare-proc", in.asFormals, out.asFormals)
    case (Nil, Some(Spec(mod, pre, post))) =>
      List(
        "declare-proc",
        in.asFormals,
        out.asFormals,
        ":modifies",
        mod,
        ":precondition",
        pre,
        ":postcondition",
        post
      )
  }

  def bexpr = cuvee.undefined
}

case class DefineProc(
    name: Name,
    params: List[Param],
    in: List[Var],
    out: List[Var],
    spec: Option[Spec],
    body: Prog
) extends Decl {
  def sexpr = (params, spec) match {
    case (Nil, None) =>
      List("define-proc", in.asFormals, out.asFormals, body)
    case (Nil, Some(Spec(mod, pre, post))) =>
      List(
        "declare-proc",
        in.asFormals,
        out.asFormals,
        ":modifies",
        mod,
        ":precondition",
        pre,
        ":postcondition",
        post,
        body
      )

  }

  def bexpr = cuvee.undefined
}

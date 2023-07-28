package cuvee.smtlib

import cuvee.pure._

import cuvee.boogie
import cuvee.sexpr
import scala.reflect.ClassTag
import cuvee.prove.Tactic
import cuvee.imp.Prog
import cuvee.util.Name
import cuvee.imp.Spec

sealed trait Res extends sexpr.Syntax {}

sealed trait IsSat extends Res
sealed trait Ack extends Res

case object Success extends Ack { def sexpr = "success" }
case object Unsupported extends Ack { def sexpr = "unsupported" }

case class Error(info: List[Any]) extends Exception with Res {
  def sexpr = "error" :: info
}

object Error extends (List[Any] => Error) {
  def apply(info: List[Any]): Nothing = {
    throw new Error(info)
  }
}

case object Sat extends IsSat { def sexpr = "sat" }
case object Unsat extends IsSat { def sexpr = "unsat" }
case object Unknown extends IsSat { def sexpr = "unknown" }

case class Model(defs: List[DefineFun]) extends Res {
  def sexpr = "model" :: defs

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

sealed trait Cmd extends sexpr.Syntax with boogie.Syntax
sealed trait Decl extends Cmd
sealed trait Ctrl extends Cmd

case object Labels extends Cmd {
  def sexpr = List("labels")
  def bexpr = cuvee.undefined
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
  def bexpr = cuvee.undefined
}

case class Pop(depth: Int) extends Ctrl {
  def sexpr = List("pop", depth)
  def bexpr = cuvee.undefined
}

case object GetModel extends Cmd {
  def sexpr = List("get-model")
  def bexpr = cuvee.undefined
}
case object Exit extends Ctrl {
  def sexpr = List("exit")
  def bexpr = cuvee.undefined
}
case object Reset extends Ctrl {
  def sexpr = List("reset")
  def bexpr = cuvee.undefined
}

case class Assert(expr: Expr) extends Cmd {
  def sexpr = List("assert", expr)
  def bexpr = List("assert", " ", expr, ";")
}

// This is part neither of SMT-LIB nor of Boogie (but we support it there).
case class Lemma(expr: Expr, tactic: Option[Tactic], assert: Boolean) extends Cmd {
  def sexpr = List("lemma", expr)
  def bexpr = tactic match {
    case None         => List("lemma", " ", expr, ";")
    case Some(tactic) => List("lemma", " ", expr, "proof", tactic, ";")
  }
}

// object Lemma extends ((Expr, Option[Tactic]) => Lemma) {
//   def apply(expr: Expr, tactic: Option[Tactic]): Lemma = {
//     Lemma(expr, tactic, true)
//   }
// }

case object CheckSat extends Cmd {
  def sexpr = List("check-sat")
  def bexpr = cuvee.undefined
}

case class DeclareSort(name: Name, arity: Int) extends Decl {
  def sexpr = List("declare-sort", name, arity)
  def bexpr = List("type", " ", name, ";")
}
case class DefineSort(name: Name, params: List[Param], body: Type) extends Decl {
  def sexpr = List("define-sort", name, params, body)
  def bexpr = cuvee.undefined // TODO: Is this right?
}

case class DeclareFun(name: Name, params: List[Param], args: List[Type], res: Type) extends Decl {
  // require(params.isEmpty, "generic functions are currently not supported")
  def sexpr = List("declare-fun", name, args, res)
  def bexpr = List("function", " ", name, "(", args, ")", ":", res)
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

case class DeclareDatatypes(arities: List[(Name, Int)], datatypes: List[Datatype]) extends Decl {
  def sexpr = List("declare-datatypes", arities, datatypes)
  def bexpr = List(
    "/* ",
    "declare-datatypes",
    " arities: ",
    arities,
    ", commands: ",
    datatypes,
    "*/"
  ) // What should we do here?
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
        ":modfies",
        mod,
        ":precondition",
        pre,
        ":postcondition" + post
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
        ":modfies",
        mod,
        ":precondition",
        pre,
        ":postcondition" + post,
        body
      )

  }

  def bexpr = cuvee.undefined
}

package cuvee.smtlib

import cuvee.error
import cuvee.util.Name
import cuvee.imp.Spec

trait Syntax extends cuvee.util.Syntax {
  def sexpr: Any
}

class SyntaxList(xs: List[Syntax]) {
  def sexpr = xs map (_.sexpr)
}

object Printer extends cuvee.util.Printer {
  def lines(any: Any): List[String] = any match {
    // Boolean values
    case true  => List("true")
    case false => List("false")
    // Numbers
    case i: Int    => List(i.toString)
    case i: BigInt => List(i.toString)
    case f: Float  => List(f.toString)
    // Name
    case n: Name => List(cuvee.sexpr.mangle(n.toLabel))
    // Syntax from Cmd
    case Success              => wrapper("success")
    case Unsupported          => wrapper("unsupported")
    case Error(info)          => wrapper("error" :: info)
    case Sat                  => wrapper("sat")
    case Unsat                => wrapper("unsat")
    case Unknown              => wrapper("unknown")
    case Model(defs)          => wrapper("model" :: defs)
    case Labels               => wrapper("labels")
    case SetLogic(logic)      => wrapper("set-logic", logic)
    case SetOption(attr, arg) => wrapper("set-option", ":" + attr, arg)
    case GetInfo(attr)        => wrapper("get-info", ":" + attr)
    case Push(depth)          => wrapper("push", depth)
    case Pop(depth)           => wrapper("pop", depth)
    case GetModel             => wrapper("get-model")
    case Exit                 => wrapper("exit")
    case Reset                => wrapper("reset")
    case Assert(expr)         => wrapper("assert", expr)
    case CheckSat             => wrapper("check-sat")
    case SetInfo(attr, arg) if arg == None => wrapper("set-info", ":" + attr)
    case SetInfo(attr, arg)          => wrapper("set-info", ":" + attr, arg)
    case Lemma(expr, tactic, assert) => wrapper("lemma", expr)
    case DeclareSort(name, arity)    => wrapper("declare-sort", name, arity)
    case DefineSort(name, params, body) =>
      wrapper("define-sort", name, params, body)
    case DeclareFun(name, params, args, res) =>
      wrapper("declare-fun", name, args, res)
    case DefineFun(name, params, formals, res, body, rec) if rec =>
      wrapper("define-fun-rec", name, formals.asFormals, res, body)
    case DefineFun(name, params, formals, res, body, rec) =>
      wrapper("define-fun", name, formals.asFormals, res, body)
    case DeclareDatatypes(arities, datatypes) =>
      wrapper("declare-datatypes", arities, datatypes)
    case DeclareProc(name, params, in, out, spec) =>
      (params, spec) match {
        case (Nil, None) => wrapper("declare-proc", in.asFormals, out.asFormals)
        case (Nil, Some(Spec(mod, pre, post))) =>
          wrapper(
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
    case DefineProc(name, params, in, out, spec, body) =>
      (params, spec) match {
        case (Nil, None) =>
          wrapper("define-proc", in.asFormals, out.asFormals, body)
        case (Nil, Some(Spec(mod, pre, post))) =>
          wrapper(
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
    // Syntax from Expr
    // TODO

    case s: Syntax => lines(s.sexpr)
    case s: String => List(s)
    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => printApp(lines(a) ++ lines(b))
    case xs: List[_] => printApp(xs flatMap lines)
  }

  def wrapper(args: Any*) = printApp(args.toList flatMap lines)

  def printApp(args: List[String]): List[String] = {
    if (args.isEmpty) {
      List("()")
    } else {
      val max = args.maxBy(_.length)
      val sum = args.foldLeft(0)(_ + _.length)

      val break =
        args.length >= 2 && (max.length > 20 || sum >= 80)

      if (break) {
        val first :: rest = args
        ("(" + first) :: indent(rest)
      } else {
        List(args.mkString("(", " ", ")"))
      }
    }
  }

  def indent(lines: List[String]): List[String] = lines match {
    case List(last)    => List("  " + last + ")")
    case first :: rest => ("  " + first) :: indent(rest)
  }
}

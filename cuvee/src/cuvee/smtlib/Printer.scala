package cuvee.smtlib

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._
import cuvee.sexpr

trait Syntax extends cuvee.util.Syntax {
  def sexpr: Any
}

class SyntaxList(xs: List[Syntax]) {
  def sexpr = xs map (_.sexpr)
}

object Printer extends cuvee.util.Printer {
  def just(any: Any): List[String] =
    List(any.toString)

  def args(args: Any*) = {
    args.toList
  }

  def args2(args: Any*)(rest: List[Any]) = {
    args.toList ++ rest
  }

  def parens(args: Any*) = {
    printApp(args.toList flatMap lines)
  }

  def parens2(args: Any*)(rest: List[Any]) = {
    printApp(args.toList ++ rest flatMap lines)
  }

  def lines(any: Any): List[String] = any match {
    // Boolean values
    case true  => just("true")
    case false => just("false")

    // Basic Types
    case i: Int    => just(i)
    case i: BigInt => just(i)
    case s: String => just(s)
    case f: Float  => just(f)

    // Name
    case n: Name => List(cuvee.sexpr.mangle(n.toLabel))

    // smtlib.Cmd
    case Success                  => just("success")
    case Unsupported              => just("unsupported")
    case Error(info)              => parens2("error")(info)
    case Sat                      => just("sat")
    case Unsat                    => just("unsat")
    case Unknown                  => just("unknown")
    case Model(defs)              => parens2("model")(defs)
    case Labels                   => parens("labels")
    case SetLogic(logic)          => parens("set-logic", logic)
    case SetOption(attr, arg)     => parens("set-option", ":" + attr, arg)
    case GetInfo(attr)            => parens("get-info", ":" + attr)
    case Push(depth)              => parens("push", depth)
    case Pop(depth)               => parens("pop", depth)
    case GetModel                 => parens("get-model")
    case Exit                     => parens("exit")
    case Reset                    => parens("reset")
    case Assert(expr)             => parens("assert", expr)
    case CheckSat                 => parens("check-sat")
    case Lemma(expr, _, _)        => parens("lemma", expr)
    case SetInfo(attr, None)      => parens("set-info", ":" + attr)
    case SetInfo(attr, Some(arg)) => parens("set-info", ":" + attr, arg)

    case DeclareSort(name, arity) =>
      parens("declare-sort", name, arity)
    case DefineSort(name, params, body) =>
      parens("define-sort", name, params, body)
    case DeclareFun(name, params, args, res) =>
      parens("declare-fun", name, args, res)
    case DefineFun(name, params, formals, res, body, rec) if rec =>
      parens("define-fun-rec", name, formals.asFormals, res, body)
    case DefineFun(name, params, formals, res, body, _) =>
      parens("define-fun", name, formals.asFormals, res, body)
    case DeclareDatatypes(arities, datatypes) =>
      parens("declare-datatypes", arities, datatypes)

    case DeclareProc(name, params, in, out, None) =>
      parens("declare-proc", in.asFormals, out.asFormals)

    case DeclareProc(name, params, in, out, Some(Spec(mod, pre, post))) =>
      parens(
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

    case DefineProc(name, Nil, in, out, None, body) =>
      parens("define-proc", in.asFormals, out.asFormals, body)

    case DefineProc(name, Nil, in, out, Some(Spec(mod, pre, post)), body) =>
      parens(
        "define-proc",
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

    // pure.Expr
    case Lit(a, _)             => just(a)
    case Var(name, _)          => lines(name)
    case Is(arg, fun)          => parens(args("_", "is", fun.name), arg)
    case Case(pat, expr)       => parens(pat, expr)
    case Match(expr, cases, _) => parens("match", expr, cases)
    case LetEq(x, e)           => parens(x, e)
    case Let(eqs, body)        => parens("let", eqs, body)
    case Note(expr, attr)      => parens2("!", expr)(attr)
    case Distinct(exprs)       => parens2("distinct")(exprs)

    case Bind(quant, formals, body, _) =>
      parens(quant.name, formals.asFormals, body)

    case App(inst, Nil) =>
      lines(inst)

    // constant array
    case Const(arg) => parens(args("as", "const", arg.typ), arg)

    case And(phis) => parens2("and")(phis)
    case Or(phis)  => parens2("or")(phis)

    case App(inst, args) =>
      parens2(inst.fun.name)(args)

    // pure.Fun
    case Inst(fun, ty) if fun.params.nonEmpty =>
      parens("as", fun.name, fun.res subst ty)
    case Inst(fun, ty) =>
      lines(fun.name)

    // pure.Prop
    case Atom(expr, _) =>
      lines(expr)
    case Conj(xs, neg) =>
      parens2("exists", xs.asFormals, "or")(neg)
    case Disj(xs, neg, pos) =>
      parens("forall", xs.asFormals, args("=>", args2("and")(neg), args2("or")(pos)))

    // pure.Type
    case Datatype(params, constrs) =>
      val constrs_ = for ((k, sels) <- constrs) yield {
        val sels_ = for (sel <- sels) yield {
          args(sel.name, sel.res)
        }
        k.name :: sels_
      }

      if (params.isEmpty)
        lines(constrs_)
      else
        parens("par", params, constrs_)

    case Param(name)    => lines(name)
    case Sort(con, Nil) => lines(con.name)

    case Sort(con, args) => parens2(con.name)(args)

    // imp.Prog
    case Block(progs)        => parens2("block")(progs)
    case Break               => parens("break")
    case Return              => parens("return")
    case Local(xs, rhs)      => parens("local", (xs.asFormals zip rhs))
    case Assign(xs, rhs)     => parens("assign", xs zip rhs)
    case Spec(xs, pre, post) => parens("spec", xs, pre, post)
    case Call(name, in, out) => parens("call", name, in, out)

    case If(test, left, right) =>
      parens("if", test, left, right)

    case While(test, body, _, inv, sum, _) =>
      parens("while", test, body, ":invariant", inv, ":summary", sum)

    // sexpr.Expr
    case lit: sexpr.Lit  => lines(lit.toString) // TODO which toString is this?
    case sexpr.Kw(name)  => parens(":" + name)
    case sexpr.Id(name)  => parens(name)
    case sexpr.App(args) => parens(args)

    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => printApp(lines(a) ++ lines(b))
    case xs: List[_] => printApp(xs flatMap lines)
  }

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

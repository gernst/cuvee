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
    // smtlib.Cmd
    case Success              => lines("success")
    case Unsupported          => lines("unsupported")
    case Error(info)          => wrapper2("error")(info)
    case Sat                  => lines("sat")
    case Unsat                => lines("unsat")
    case Unknown              => lines("unknown")
    case Model(defs)          => wrapper2("model")(defs)
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
    case Lemma(expr, _, _)    => wrapper("lemma", expr)
    case SetInfo(attr, arg) if arg == None => wrapper("set-info", ":" + attr)
    case SetInfo(attr, arg) => wrapper("set-info", ":" + attr, arg)
    case DeclareSort(name, arity) =>
      wrapper("declare-sort", name, arity)
    case DefineSort(name, params, body) =>
      wrapper("define-sort", name, params, body)
    case DeclareFun(name, params, args, res) =>
      wrapper("declare-fun", name, args, res)
    case DefineFun(name, params, formals, res, body, rec) if rec =>
      wrapper("define-fun-rec", name, formals.asFormals, res, body)
    case DefineFun(name, params, formals, res, body, _) =>
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
    // pure.Expr
    case Var(name, _)          => lines(name)
    case Lit(a, _)             => lines(a.toString)
    case Is(arg, fun)          => wrapper(wrapper("_", "is", fun.name), arg)
    case Case(pat, expr)       => wrapper(pat, expr)
    case Match(expr, cases, _) => wrapper("match", expr, cases)
    case LetEq(x, e)           => wrapper(x, e)
    case Let(eqs, body)        => wrapper("let", eqs, body)
    case Note(expr, attr) =>
      wrapper2("!", expr)(attr) // TODO was comment: def sexpr = "!" :: expr :: attr FIX: it should actually be like that
    case Distinct(exprs) => wrapper2("distinct")(exprs)
    case Bind(quant, formals, body, _) =>
      wrapper(quant.name, formals.asFormals, body)
    case app@App(inst, args) => // TODO: what about this? ANSWER: this is the object being matched, we can bind it as shown
      app match {
        case And(phis)  => wrapper2("and")(phis)
        case Or(phis)   => wrapper2("or")(phis)
        case Const(arg) => wrapper(wrapper("as", "const", inst.res), arg)
        case _ if args.isEmpty && inst.params.nonEmpty => wrapper(inst)
        case _ if args.isEmpty                         => wrapper(inst.fun.name)
        case _ => wrapper2(inst.fun.name)(args)
      }
    // pure.Fun
    case Inst(fun, ty) => wrapper("as", fun.name, fun.res subst ty)
    // pure.Prop
    case Atom(expr, _) => wrapper(expr)
    case Conj(xs, neg) => wrapper2("exists", xs.asFormals, "or")(neg)
    case Disj(xs, neg, pos) =>
      wrapper("forall", xs.asFormals, wrapper("=>", wrapper2("and")(neg), wrapper2("or")(pos)))
    // pure.Type
    case Datatype(params, constrs) =>
      val constrs_ = for ((k, sels) <- constrs) yield {
        val sels_ = for (sel <- sels) yield {
          List(sel.name, sel.res)
        }
        k.name :: sels_
      }
      if (params.isEmpty)
        wrapper(constrs_)
      else
        wrapper("par", params, constrs_)
    case Param(name)                     => wrapper(name)
    case Sort(con, args) if args.isEmpty => wrapper(con.name)
    case Sort(con, args)                 => wrapper2(con.name)(args)
    // imp.Prog
    case Block(progs)        => wrapper2("block")(progs)
    case Break               => wrapper("break")
    case Return              => wrapper("return")
    case Local(xs, rhs)      => wrapper("local", (xs.asFormals zip rhs))
    case Assign(xs, rhs)     => wrapper("assign", xs zip rhs)
    case Spec(xs, pre, post) => wrapper("spec", xs, pre, post)
    case Call(name, in, out) => wrapper("call", name, in, out)
    case If(test, left, right) =>
      wrapper("if", test, left, right) // TODO typo? was "id" in Prog (yes)
    case While(test, body, _, inv, sum, _) =>
      wrapper("while", test, body, ":invariant", inv, ":summary", sum)
    // sexpr.Expr
    case lit: sexpr.Lit => wrapper(lit.toString) // TODO which toString is this?
    case sexpr.Kw(name)  => wrapper(":" + name)
    case sexpr.Id(name)  => wrapper(name)
    case sexpr.App(args) => wrapper(args)

    case s: Syntax => lines(s.sexpr)
    case s: String => List(s)
    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => printApp(lines(a) ++ lines(b))
    case xs: List[_] => printApp(xs flatMap lines)
  }

  def wrapper(args: Any*) = {
    printApp(args.toList flatMap lines)
  }

  def wrapper2(args: Any*)(rest: List[Any]) = {
    printApp(args.toList ++ rest flatMap lines)
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

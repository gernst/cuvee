package cuvee.smtlib

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._
import cuvee.sexpr
import cuvee.imp.traces.Trace

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

    case Mode.In    => just("in")
    case Mode.Out   => just("out")
    case Mode.InOut => just("inout")

    case Loc(name) => just(name)

    // Name
    case n: Name => List(cuvee.sexpr.mangle(n.toLabel))

    // smtlib.Cmd
    case Success              => just("success")
    case Unsupported          => just("unsupported")
    case Info(arg)            => lines(arg)
    case Labels(labels)       => parens2("labels")(labels)
    case Error(info)          => parens2("error")(info)
    case Sat                  => just("sat")
    case Unsat                => just("unsat")
    case Unknown              => just("unknown")
    case Model(defs)          => parens2("model")(defs)
    case Labels               => parens("labels")
    case SetLogic(logic)      => parens("set-logic", logic)
    case SetOption(attr, arg) => parens("set-option", ":" + attr, arg)
    case GetInfo(attr)        => parens("get-info", ":" + attr)
    case Push(depth)          => parens("push", depth)
    case Pop(depth)           => parens("pop", depth)
    case GetModel             => parens("get-model")
    case Apply(tactic)        => parens("apply", tactic)
    case Exit                 => parens("exit")
    case Reset                => parens("reset")
    case Assert(expr)         => parens("assert", expr)
    case CheckSat             => parens("check-sat")
    // TODO
    case Lemma(expr, _, Some(Goal), _) => parens("goal", expr)
    case Lemma(expr, _, Some(Free), _) => parens("free lemma", expr)
    case Lemma(expr, _, _, _)          => parens("lemma", expr)
    case SetInfo(attr, None)           => parens("set-info", ":" + attr)
    case SetInfo(attr, Some(arg))      => parens("set-info", ":" + attr, arg)

    case DeclareSort(name, arity) =>
      parens("declare-sort", name, arity)

    case DefineSort(name, params, body) =>
      parens("define-sort", name, params, body)

    case DeclareVar(name, typ) => // not in SMT-LIB
      parens("declare-var", name, typ)

    case DeclareFun(name, Nil, args, res) =>
      parens("declare-fun", name, args, res)

    // support parameters in alt-ergo format
    case DeclareFun(name, params, args, res) =>
      parens("declare-fun", name, parens("par", parens(params), args, res))

    case DefineFun(name, Nil, formals, res, body, true) =>
      parens("define-fun-rec", name, formals.asFormals, res, body)

    case DefineFun(name, params, formals, res, body, true) =>
      parens("define-fun-rec", name, parens("par", parens(params), formals.asFormals, res, body))

    case DefineFun(name, Nil, formals, res, body, false) =>
      parens("define-fun", name, formals.asFormals, res, body)

    case DefineFun(name, params, formals, res, body, false) =>
      parens("define-fun", name, parens("par", parens(params), formals.asFormals, res, body))

    case DeclareDatatypes(arities, datatypes) =>
      parens("declare-datatypes", arities, datatypes)

    case DeclareAbstractions(arities, datatypes) =>
      parens("declare-abstractions", arities, datatypes)

    case DeclareProc(name, Nil, in, out, None) =>
      parens("declare-proc", in.asFormals, out.asFormals)

    case DeclareProc(name, Nil, in, out, Some(Spec(mod, pre, post))) =>
      // XXX: not K3
      parens(
        "declare-proc",
        name,
        in.asFormals,
        out.asFormals,
        ":modifies",
        mod,
        ":precondition",
        pre,
        ":postcondition",
        post
      )

    case DeclareContracts(name, params, formals, contracts) =>
      parens("declare-contract", name, formals, contracts)

    case DefineProc(name, Nil, in, out, None, body) =>
      val avoid = in ++ out
      val (local, body_) = Prog.liftLocals(avoid.toSet, body)
      parens("define-proc", name, in.asFormals, out.asFormals, local.asFormals, body_)

    case DefineProc(name, Nil, in, out, Some(Spec(mod, pre, post)), body) =>
      val avoid = in ++ out
      val (local, body_) = Prog.liftLocals(avoid.toSet, body)
      val attr = List(":modifies", mod, ":requires", pre, ":ensures", post)
      parens(
        "define-proc",
        name,
        in.asFormals,
        out.asFormals,
        local.asFormals,
        parens2("!", body_)(attr)
      )

    // pure.Expr
    case Lit(i: BigInt, _) =>
      if (i >= 0) just(i) else just("(- " + (-i) + ")")

    case Lit(s: String, _) =>
      just("\"" + s + "\"")

    case Var(name, _)          => lines(name)
    case At(loc, expr)         => parens(loc, expr)
    case Is(arg, fun)          => parens(args("_", "is", fun.name), arg)
    case Case(pat, expr)       => parens(pat, expr)
    case Match(expr, cases, _) => parens("match", expr, cases)
    case LetEq(x, e)           => parens(x, e)
    case Let(eqs, body)        => parens("let", eqs, body)
    case Distinct(exprs)       => parens2("distinct")(exprs)

    case note @ cuvee.imp.Note(prog, attrs) =>
      parens2("!", prog)(attrs.flatten)

    case note @ cuvee.pure.Note(expr, patterns, attrs) =>
      val extra = patterns map (":pattern" :: _)
      parens2("!", expr)(extra.flatten ++ attrs.flatten)

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

    case Trace(init, iteration, acc, updates) =>
      parens()

    // pure.Fun
    case Inst(fun, ty) if fun.params.nonEmpty =>
      parens("as", fun.name, fun.res subst ty)
    case Inst(fun, ty) =>
      lines(fun.name)

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
    case Block(progs)    => parens2("sequence")(progs)
    case Break           => parens("break")
    case Return          => parens("return")
    case Local(xs, Nil)  => parens("local", xs.asFormals)
    case Local(xs, rhs)  => parens("local", (xs.asFormals zip rhs))
    case Assign(xs, rhs) => parens("assign", xs zip rhs)

    case Spec(Nil, True, post) => parens("assume", post)
    case Spec(Nil, pre, True)  => parens("assert", pre)
    case Spec(xs, True, True)  => parens("havoc", xs)
    case Spec(xs, pre, post)   => parens("spec", xs, pre, post)

    case Call(name, in, out) => parens("call", name, in, out)

    case If(test, left, Skip) =>
      parens("if", test, left)

    case If(test, left, right) =>
      parens("if", test, left, right)

    case While(test, body, Zero, True, True, Nil) =>
      parens("while", test, body)

    case While(test, body, term, inv, True, Nil) =>
      val attr = List(":decreases", term, ":invariant", inv)
      parens2("!", parens("while", test, body))(attr)

    case While(test, body, term, inv, sum, Nil) =>
      val attr = List(":decreases", term, ":requires", inv, ":ensures", sum)
      parens2("!", parens("while", test, body))(attr)

    // sexpr.Expr
    case lit: sexpr.Lit       => just(lit)
    case sexpr.Kw(name)       => just(":" + name)
    case sexpr.Id(name)       => just(cuvee.sexpr.mangle(name))
    case sexpr.App(args @ _*) => lines(args.toList)

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
        val prefix = "  "
        val first :: rest = args
        ("(" + first) :: indent(prefix, rest)
      } else {
        List(args.mkString("(", " ", ")"))
      }
    }
  }

  def indent(prefix: String, lines: List[String]): List[String] = lines match {
    case List(last)    => List(prefix + last + ")")
    case first :: rest => (prefix + first) :: indent(prefix, rest)
  }
}

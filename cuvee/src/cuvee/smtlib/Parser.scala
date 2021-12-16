package cuvee.smtlib

import cuvee.fail
import cuvee.pure.Type
import cuvee.pure.State
import cuvee.sexpr._
import cuvee.pure.Param
import cuvee.pure.Datatype
import cuvee.pure.Fun
import cuvee.pure.Sort
import cuvee.pure.Var

class Parser(val st: State) {
  import st._

  val int = sort("Int")
  val real = sort("Real")
  val bool = sort("Bool")

  def cmd(from: Expr): Cmd =
    from match {
      case App(Id("set-logic"), Lit.str(logic)) =>
        SetLogic(logic)

      case App(Id("set-option"), args @ _*) =>
        fail("unsupported command: " + from)

      case App(Id("set-info"), Kw(attr)) =>
        SetInfo(attr, None)

      case App(Id("set-info"), Kw(attr), arg) =>
        SetInfo(attr, Some(arg))

      case Id("get-model")      => GetModel
      case Id("exit")           => Exit
      case Id("reset")          => Reset
      case Id("get-assertions") => GetAssertions
      case Id("check-sat")      => CheckSat

      case App(Id("push"), Lit.num(digits)) =>
        Push(digits.toInt)

      case App(Id("pop"), Lit.num(digits)) =>
        Pop(digits.toInt)

      case App(Id("assert"), phi) =>
        object exprs extends Exprs
        Assert(exprs(phi))

      case App(Id("declare-sort"), Id(name), Lit.num(digits)) =>
        val n = digits.toInt
        con(name, n)
        DeclareSort(name, n)

      case App(Id("define-sort"), Id(name), App(args @ _*), res) =>
        val params_ = params(args.toList)
        val n = params_.length
        val res_ = typ(res)
        con(name, n)
        condef(name, params_, res_)
        DefineSort(name, params_, res_)

      case App(Id("declare-const"), Id(name), res) =>
        val args_ = Nil
        val res_ = typ(res)
        fun(name, Nil, args_, res_)
        DeclareFun(name, args_, res_)

      case App(Id("declare-fun"), Id(name), App(args @ _*), res) =>
        val args_ = types(args.toList)
        val res_ = typ(res)
        fun(name, Nil, args_, res_)
        DeclareFun(name, args_, res_)

      case App(Id(cmd), Id(name), App(args @ _*), res, expr)
          if cmd == "define-fun" || cmd == "define-fun-rec" =>
        val formals_ = formals(args.toList)
        val res_ = typ(res)
        fun(name, Nil, formals_.types, res_)

        object exprs extends Exprs
        val body_ = exprs(expr, formals_.pairs)
        fundef(name, formals_, body_)

        DefineFun(name, formals_, res_, body_, cmd == "define-fun-rec")

      case App(
            Id("declare-datatype"),
            Id(name),
            from @ App(Id("par"), App(args @ _*), App(alts @ _*))
          ) =>
        val decl = (name, args.length)
        val List(dt) = datatypes(List(decl), List(from))
        DeclareDatatypes(List(decl), List(dt))

      case App(Id("declare-datatype"), Id(name), from @ App(alts @ _*)) =>
        val decl = (name, 0)
        val List(dt) = datatypes(List(decl), List(from))
        DeclareDatatypes(List(decl), List(dt))

      case App(Id("declare-datatypes"), App(names @ _*), App(froms @ _*)) =>
        val decls = arities(names.toList)
        val dts = datatypes(decls, froms.toList)
        DeclareDatatypes(decls, dts)

      case _ =>
        fail("invalid command: " + from)
    }

  def datatypes(
      decls: List[(String, Int)],
      froms: List[Expr]
  ): List[Datatype] = {
    for (((name, arity), from) <- decls zip froms)
      yield {
        con(name, arity)
        datatype(name, arity, from)
      }
  }

  def sel(params: List[Param], in: Sort, from: Expr): Fun =
    from match {
      case App(Id(name), arg) =>
        val out = typ(arg)
        Fun(name, params, List(in), out)

      case _ =>
        fail("invalid selector declaration: " + from)
    }

  def constr(params: List[Param], typ: Sort, from: Expr): (Fun, List[Fun]) =
    from match {
      case App(Id(name), args @ _*) =>
        val sels_ = sels(params, typ, args.toList)
        val types = sels_ map (_.res)
        fun(name, params, types, typ) -> sels_

      case _ =>
        fail("invalid constructor declaration: " + from)
    }

  def datatype(name: String, arity: Int, from: Expr): Datatype =
    from match {
      case App(Id("par"), App(args @ _*), App(alts @ _*)) =>
        val params_ = params(args.toList)
        val typ = sort(name, params_)
        Datatype(params_, constrs(params_, typ, alts.toList))

      case App(alts @ _*) =>
        val params_ = Nil
        val typ = sort(name)
        Datatype(params_, constrs(params_, typ, alts.toList))

      case _ =>
        fail("invalid datatype declaration: " + from)
    }

  def arity(from: Expr) =
    from match {
      case App(Id(name), Lit.num(digits)) =>
        (name, digits.toInt)
      case _ =>
        fail("invalid arity declaration: " + from)
    }

  def array(dom: Type, ran: Type) =
    sort("Array", List(dom, ran))

  def formal(from: Expr): Var =
    from match {
      case App(Id(name), what) =>
        Var(name, typ(what))
      case _ =>
        fail("invalid formal parameter: " + from)
    }

  def param(from: Expr): Param =
    from match {
      case Id(name) =>
        Param(name)
      case _ =>
        fail("invalid type parameter: " + from)
    }

  def typ(from: Expr): Type =
    from match {
      case Id(name) =>
        sort(name)
      case App(Id(name), args @ _*) =>
        sort(name, types(args.toList))
      case _ =>
        fail("invalid type: " + from)
    }

  def formals(from: List[Expr]): List[Var] =
    from map formal

  def types(from: List[Expr]): List[Type] =
    from map typ

  def params(from: List[Expr]): List[Param] =
    from map param

  def arities(from: List[Expr]): List[(String, Int)] =
    from map arity

  def sels(
      params: List[Param],
      res: Sort,
      from: List[Expr]
  ): List[Fun] =
    from map { sel(params, res, _) }

  def constrs(
      params: List[Param],
      res: Sort,
      from: List[Expr]
  ): List[(Fun, List[Fun])] =
    from map { constr(params, res, _) }

  class Exprs extends st.Exprs {
    def apply(
        from: Expr,
        scope: Iterable[(String, Type)] = Map()
    ) = {
      val pre = expr(from, scope.toMap)
      pre.resolve
    }

    def expr(from: Expr, scope: Map[String, Type]): Pre =
      from match {
        case Lit.num(digits) =>
          lit(digits.toInt, int)

        case Lit.dec(digits) =>
          lit(digits.toDouble, real)

        case Id(name) if scope contains name =>
          x(name, scope(name))

        case Id(name) if funs contains name =>
          const(name)

        case App(Id(name), args @ _*) if funs contains name =>
          app(name, exprs(args.toList, scope))

        case App(Id(name), App(bound @ _*), arg)
            if name == "exists" | name == "forall" =>
          val xs = formals(bound.toList)
          val body = expr(arg, scope ++ xs.pairs)
          check(body, bool)
          bind(name, xs, body, bool)

        case App(Id(name), App(bound), arg) if name == "lambda" =>
          val x @ Var(name, dom, _) = formal(bound)
          val body = expr(arg, scope + (name -> dom))
          bind(name, List(x), body, array(dom, body.typ))

        case _ =>
          fail("invalid expression: " + from)
      }

    def exprs(
        from: List[Expr],
        scope: Map[String, Type]
    ): List[Pre] = {
      from map (expr(_, scope))
    }
  }
}

package cuvee.smtlib

import cuvee.error
import cuvee.pure.Type
import cuvee.pure.State
import cuvee.sexpr._
import cuvee.pure.Param
import cuvee.pure.Datatype
import cuvee.pure.Fun
import cuvee.pure.Sort
import cuvee.pure.Var

class Parser(init: State) {
  // import st._
  var stack = List(init)
  def st = stack.head

  val int = st.sort("Int")
  val bool = st.sort("Bool")
  val real = st.sort("Real")

  val ctx0: Set[String] = Set()

  def ack(from: Expr): Ack =
    from match {
      case Id("success") => Success
      case _ =>
        error("invalid ack: " + from)
    }

  def issat(from: Expr): IsSat =
    from match {
      case Id("sat")     => Sat
      case Id("unsat")   => Unsat
      case Id("unknown") => Unknown
      case _ =>
        error("invalid status: " + from)
    }

  def cmd(from: Expr): Cmd =
    from match {
      case App(Id("set-logic"), Lit.str(logic)) =>
        SetLogic(logic)

      case App(Id("set-option"), args @ _*) =>
        error("unsupported command: " + from)

      case App(Id("set-info"), Kw(attr)) =>
        SetInfo(attr, None)

      case App(Id("set-info"), Kw(attr), arg) =>
        SetInfo(attr, Some(arg))

      case App(Id("get-model"))      => GetModel
      case App(Id("exit"))           => Exit
      case App(Id("reset"))          => Reset
      case App(Id("get-assertions")) => GetAssertions
      case App(Id("check-sat"))      => CheckSat

      case App(Id("push"), Lit.num(digits)) =>
        stack = stack.tail
        Push(digits.toInt)

      case App(Id("pop"), Lit.num(digits)) =>
        stack = stack.head :: stack
        Pop(digits.toInt)

      case App(Id("assert"), phi) =>
        val phi_ = expr_typed(phi, bool)
        Assert(phi_)

      case App(Id("declare-sort"), Id(name), Lit.num(digits)) =>
        val n = digits.toInt
        st.con(name, n)
        DeclareSort(name, n)

      case App(Id("define-sort"), Id(name), App(args @ _*), res) =>
        val params_ = params(args.toList)
        val n = params_.length
        val res_ = typ(res)
        st.con(name, n)
        st.condef(name, params_, res_)
        DefineSort(name, params_, res_)

      case App(Id("declare-const"), Id(name), res) =>
        val args_ = Nil
        val res_ = typ(res)
        st.fun(name, Nil, args_, res_)
        DeclareFun(name, args_, res_)

      case App(Id("declare-fun"), Id(name), App(args @ _*), res) =>
        val args_ = types(args.toList)
        val res_ = typ(res)
        st.fun(name, Nil, args_, res_)
        DeclareFun(name, args_, res_)

      case App(Id(cmd), Id(name), App(args @ _*), res, body)
          if cmd == "define-fun" || cmd == "define-fun-rec" =>
        val formals_ = formals(args.toList)
        val res_ = typ(res)
        st.fun(name, Nil, formals_.types, res_)

        val body_ = expr_typed(body, res_, ctx0, formals_.pairs)
        st.fundef(name, formals_, body_)

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
        error("invalid command: " + from)
    }

  def datatypes(
      decls: List[(String, Int)],
      froms: List[Expr]
  ): List[Datatype] = {
    for (((name, arity), from) <- decls zip froms)
      yield {
        st.con(name, arity)
        datatype(name, arity, from)
      }
  }

  def sel(params: List[Param], in: Sort, from: Expr, ctx: Set[String]): Fun =
    from match {
      case App(Id(name), arg) =>
        val out = typ(arg, ctx)
        Fun(name, params, List(in), out)

      case _ =>
        error("invalid selector declaration: " + from)
    }

  def constr(
      params: List[Param],
      typ: Sort,
      from: Expr,
      ctx: Set[String]
  ): (Fun, List[Fun]) =
    from match {
      case App(Id(name), args @ _*) =>
        val sels_ = sels(params, typ, args.toList, ctx)
        val types = sels_ map (_.res)
        st.fun(name, params, types, typ) -> sels_

      case _ =>
        error("invalid constructor declaration: " + from)
    }

  def datatype(name: String, arity: Int, from: Expr): Datatype =
    from match {
      case App(Id("par"), App(args @ _*), App(alts @ _*)) =>
        val params_ = params(args.toList)
        val typ = st.sort(name, params_)
        val ctx = params_.names.toSet
        Datatype(params_, constrs(params_, typ, alts.toList, ctx))

      case App(alts @ _*) =>
        val params_ = Nil
        val typ = st.sort(name)
        Datatype(params_, constrs(params_, typ, alts.toList, ctx0))

      case _ =>
        error("invalid datatype declaration: " + from)
    }

  def arity(from: Expr) =
    from match {
      case App(Id(name), Lit.num(digits)) =>
        (name, digits.toInt)
      case _ =>
        error("invalid arity declaration: " + from)
    }

  def array(dom: Type, ran: Type) =
    st.sort("Array", List(dom, ran))

  def formal(from: Expr, ctx: Set[String] = Set()): Var =
    from match {
      case App(Id(name), what) =>
        Var(name, typ(what, ctx))
      case _ =>
        error("invalid formal parameter: " + from)
    }

  def param(from: Expr): Param =
    from match {
      case Id(name) =>
        Param(name)
      case _ =>
        error("invalid type parameter: " + from)
    }

  def typ(from: Expr, ctx: Set[String] = Set()): Type =
    from match {
      case Id(name) if ctx contains name =>
        Param(name)
      case Id(name) =>
        st.sort(name)
      case App(Id(name), args @ _*) =>
        st.sort(name, types(args.toList, ctx))
      case _ =>
        error("invalid type: " + from)
    }

  def cmds(from: List[Expr]): List[Cmd] =
    from map cmd

  def formals(from: List[Expr], ctx: Set[String] = Set()): List[Var] =
    from map (formal(_, ctx))

  def types(from: List[Expr], ctx: Set[String] = Set()): List[Type] =
    from map (typ(_, ctx))

  def params(from: List[Expr]): List[Param] =
    from map param

  def arities(from: List[Expr]): List[(String, Int)] =
    from map arity

  def sels(
      params: List[Param],
      res: Sort,
      from: List[Expr],
      ctx: Set[String]
  ): List[Fun] =
    from map { sel(params, res, _, ctx) }

  def constrs(
      params: List[Param],
      res: Sort,
      from: List[Expr],
      ctx: Set[String]
  ): List[(Fun, List[Fun])] =
    from map { constr(params, res, _, ctx) }

  def expr(
      from: Expr,
      ctx: Iterable[String] = Set(),
      scope: Iterable[(String, Type)] = Map()
  ) = {
    val inner = exprs(st)
    val pre = inner.expr(from, ctx.toSet, scope.toMap)
    pre.resolve
  }

  def expr_typed(
      from: Expr,
      expect: Type,
      ctx: Iterable[String] = Set(),
      scope: Iterable[(String, Type)] = Map()
  ) = {
    val inner = exprs(st)
    val pre = inner.expr(from, ctx.toSet, scope.toMap)
    inner.check(pre, expect)
    pre.resolve
  }

  def exprs(st: State) = new st.Exprs {
    def expr(from: Expr, ctx: Set[String], scope: Map[String, Type]): Pre =
      from match {
        case Lit.num(digits) =>
          lit(digits.toInt, int)

        case Lit.dec(digits) =>
          lit(digits.toDouble, real)

        case Id(name) if scope contains name =>
          x(name, scope(name))

        case Id(name) if st.funs contains name =>
          const(name)

        case App(Id(name), args @ _*) if st.funs contains name =>
          app(name, exprs(args.toList, ctx, scope))

        case App(Id(name), App(bound @ _*), arg)
            if name == "exists" | name == "forall" =>
          val xs = formals(bound.toList, ctx)
          val body = expr(arg, ctx, scope ++ xs.pairs)
          check(body, bool)
          bind(name, xs, body, bool)

        case App(Id(name), App(bound), arg) if name == "lambda" =>
          val x @ Var(name, dom, _) = formal(bound, ctx)
          val body = expr(arg, ctx, scope + (name -> dom))
          bind(name, List(x), body, array(dom, body.typ))

        case App(Id(name), arg, App(cs @ _*)) if name == "match" =>
          match_(expr(arg, ctx, scope), cases(cs.toList, ctx, scope))

        case _ =>
          error("invalid expression: " + from)
      }

    def pat(
        from: Expr,
        ctx: Set[String]
    ): (Pre, Map[String, Type]) =
      from match {
        case Id(name) =>
          (const(name), Map()) // TODO: do proper type checking in this function

        case App(Id(name), args @ _*) =>
          val fun = st funs name
          var scope: Map[String, Type] = Map()
          val args_ = (args.toList zip fun.args) map { case (Id(name), typ) =>
            scope += name -> typ
            x(name, typ)
          }
          (app(name, args_), scope)
      }

    def case_(
        from: Expr,
        ctx: Set[String],
        scope: Map[String, Type]
    ): (Pre, Pre) =
      from match {
        case App(p, e) =>
          val (p_, scope_) = pat(p, ctx)
          val e_ = expr(e, ctx, scope ++ scope_)
          (p_, e_)
        case _ =>
          error("invalid case: " + from)
      }

    def cases(
        from: List[Expr],
        ctx: Set[String],
        scope: Map[String, Type]
    ): List[(Pre, Pre)] = {
      from map (case_(_, ctx, scope))
    }

    def exprs(
        from: List[Expr],
        ctx: Set[String],
        scope: Map[String, Type]
    ): List[Pre] = {
      from map (expr(_, ctx, scope))
    }
  }
}

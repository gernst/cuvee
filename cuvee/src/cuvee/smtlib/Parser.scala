package cuvee.smtlib

import cuvee.error
import cuvee.State
import cuvee.pure.Type
import cuvee.pure.Param
import cuvee.pure.Datatype
import cuvee.pure.Fun
import cuvee.pure.Sort
import cuvee.pure.Var
import cuvee.util.Name
import cuvee.sexpr._
import cuvee.pure.LetEq

class Parser(init: State) {
  // import st._
  var stack = List(init)
  def st = stack.head

  val int = st.sort("Int")
  val bool = st.sort("Bool")
  val real = st.sort("Real")

  val ctx0: Set[Name] = Set()

  def ack(from: Expr): Ack =
    from match {
      case Id("success") =>
        Success
      case App(Id("error"), args @ _*) =>
        Error(args.toList)
      case _ =>
        error("invalid ack: " + from)
    }

  def issat(from: Expr): IsSat =
    from match {
      case Id("sat")     => Sat
      case Id("unsat")   => Unsat
      case Id("unknown") => Unknown
      case App(Id("error"), args @ _*) =>
        Error(args.toList)
      case _ =>
        error("invalid status: " + from)
    }

  def cmd(from: Expr): Cmd = cuvee.trace("bad command: " + from) {
    from match {
      case App(Id("set-logic"), Id(logic)) =>
        SetLogic(logic)

      case App(Id("set-option"), Kw(attr), arg) =>
        SetOption(attr, arg)

      case App(Id("get-info"), Kw(attr)) =>
        GetInfo(attr)

      case App(Id("set-info"), Kw(attr)) =>
        SetInfo(attr, None)

      case App(Id("set-info"), Kw(attr), arg) =>
        SetInfo(attr, Some(arg))

      case App(Id("get-model")) => GetModel
      case App(Id("labels"))    => Labels

      case App(Id("check-sat")) => CheckSat

      case App(Id("push"), Lit.num(digits)) =>
        val n = digits.toInt
        stack = List.tabulate(n)(_ => stack.head) ++ stack
        Push(n)

      case App(Id("pop"), Lit.num(digits)) =>
        val n = digits.toInt
        stack = stack drop n
        Pop(n)

      case App(Id("reset")) =>
        stack = List(init)
        Reset

      case App(Id("exit")) =>
        println("!!! exit in parser")
        cuvee.undefined
        Exit

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
        val decl = (name: Name, args.length)
        val List(dt) = datatypes(List(decl), List(from))
        DeclareDatatypes(List(decl), List(dt))

      case App(Id("declare-datatype"), Id(name), from @ App(alts @ _*)) =>
        val decl = (name: Name, 0)
        val List(dt) = datatypes(List(decl), List(from))
        DeclareDatatypes(List(decl), List(dt))

      case App(Id("declare-datatypes"), App(names @ _*), App(froms @ _*)) =>
        val decls = arities(names.toList)
        val dts = datatypes(decls, froms.toList)
        DeclareDatatypes(decls, dts)

      case _ =>
        error("invalid command: " + from)
    }
  }

  def datatypes(
      decls: List[(Name, Int)],
      froms: List[Expr]
  ): List[Datatype] = {
    for (((name, arity), from) <- decls zip froms)
      st.con(name, arity)

    for (((name, arity), from) <- decls zip froms)
      yield datatype(name, arity, from)
  }

  def sel(params: List[Param], in: Sort, from: Expr, ctx: Set[Name]): Fun =
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
      ctx: Set[Name]
  ): (Fun, List[Fun]) =
    from match {
      case App(Id(name), args @ _*) =>
        val sels_ = sels(params, typ, args.toList, ctx)
        val types = sels_ map (_.res)
        st.fun(name, params, types, typ) -> sels_

      case _ =>
        error("invalid constructor declaration: " + from)
    }

  def datatype(name: Name, arity: Int, from: Expr): Datatype =
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

  def arity(from: Expr): (Name, Int) =
    from match {
      case App(Id(name), Lit.num(digits)) =>
        (name: Name, digits.toInt)
      case _ =>
        error("invalid arity declaration: " + from)
    }

  def array(dom: Type, ran: Type) =
    st.sort("Array", List(dom, ran))

  def formal(from: Expr, ctx: Set[Name] = Set()): Var =
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

  def typ(from: Expr, ctx: Set[Name] = Set()): Type =
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

  def model(from: Expr): List[DefineFun] =
    from match {
      case App(defs @ _*) =>
        for (App(Id("define-fun"), Id(name), App(args @ _*), res, body) <- defs.toList) yield {
          val formals_ = formals(args.toList)
          val res_ = typ(res)
          val body_ = expr_typed(body, res_, ctx0, formals_.pairs)
          DefineFun(name, formals_, res_, body_, false)
        }
      case _ => cuvee.error("Unexpected format in model response")
    }

  def formals(from: List[Expr], ctx: Set[Name] = Set()): List[Var] =
    from map (formal(_, ctx))

  def types(from: List[Expr], ctx: Set[Name] = Set()): List[Type] =
    from map (typ(_, ctx))

  def params(from: List[Expr]): List[Param] =
    from map param

  def arities(from: List[Expr]): List[(Name, Int)] =
    from map arity

  def sels(
      params: List[Param],
      res: Sort,
      from: List[Expr],
      ctx: Set[Name]
  ): List[Fun] =
    from map { sel(params, res, _, ctx) }

  def constrs(
      params: List[Param],
      res: Sort,
      from: List[Expr],
      ctx: Set[Name]
  ): List[(Fun, List[Fun])] =
    from map { constr(params, res, _, ctx) }

  def expr(
      from: Expr,
      ctx: Iterable[Name] = Set(),
      scope: Iterable[(Name, Type)] = Map()
  ) = {
    val inner = exprs(st)
    val pre = inner.expr(from, ctx.toSet, scope.toMap)
    pre.resolve
  }

  def expr_typed(
      from: Expr,
      expect: Type,
      ctx: Iterable[Name] = Set(),
      scope: Iterable[(Name, Type)] = Map()
  ) = {
    val inner = exprs(st)
    val pre = inner.expr(from, ctx.toSet, scope.toMap)
    inner.check(pre, expect)
    pre.resolve
  }

  def exprs(st: State) = new st.Exprs {
    def expr(from: Expr, ctx: Set[Name], scope: Map[Name, Type]): Pre =
      from match {
        case Lit.num(digits) =>
          lit(digits.toInt, int)

        case Lit.dec(digits) =>
          lit(digits.toDouble, real)

        case Id(name) if scope contains name =>
          x(name, scope(name))

        case Id(name) if st.funs contains (name, 0) =>
          const(name)

        case App(Id("!"), from, rest @ _*) =>
          note(expr(from, ctx, scope), rest.toList)

        case App(Id("distinct"), rest @ _*) =>
          distinct(exprs(rest.toList, ctx, scope))

        case App(Id("and"), rest @ _*) =>
          commutative("and", const("true"), exprs(rest.toList, ctx, scope))

        case App(Id("or"), rest @ _*) =>
          commutative("or", const("false"), exprs(rest.toList, ctx, scope))

        case App(Id("let"), App(bound @ _*), arg) =>
          val eqs = leteqs(bound.toList, ctx, scope)
          val xs = eqs map (_._1)
          val body = expr(arg, ctx, scope ++ xs.pairs)
          let(eqs, body)

        case App(Id("lambda"), App(bound), arg) =>
          val x @ Var(name, dom) = formal(bound, ctx)
          val body = expr(arg, ctx, scope + (name -> dom))
          bind(name.toLabel, List(x), body, array(dom, body.typ))

        case App(Id("match"), arg, App(cs @ _*)) =>
          match_(expr(arg, ctx, scope), cases(cs.toList, ctx, scope))

        case App(Id(name), App(bound @ _*), arg) if name == "exists" | name == "forall" =>
          val xs = formals(bound.toList, ctx)
          val body = expr(arg, ctx, scope ++ xs.pairs)
          check(body, bool)
          bind(name, xs, body, bool)

        case App(App(Id("as"), Id(name), from), args @ _*)
            if st.funs contains (name, args.length) =>
          app(name, exprs(args.toList, ctx, scope), Some(typ(from, ctx)))

        case App(Id(name), args @ _*) if st.funs contains (name, args.length) =>
          app(name, exprs(args.toList, ctx, scope))

        case _ =>
          error("invalid expression: " + from)
      }

    def pat(
        from: Expr,
        ctx: Set[Name]
    ): (Pre, Map[Name, Type]) =
      from match {
        case Id(name) =>
          (const(name), Map()) // TODO: do proper type checking in this function

        case App(Id(name), args @ _*) =>
          val fun = st funs (name, args.length)
          var scope: Map[Name, Type] = Map()
          val args_ = (args.toList zip fun.args) map { case (Id(name), typ) =>
            val name_ : Name = name
            scope += name_ -> typ
            x(name, typ)
          }
          (app(name, args_), scope)
      }

    def case_(
        from: Expr,
        ctx: Set[Name],
        scope: Map[Name, Type]
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
        ctx: Set[Name],
        scope: Map[Name, Type]
    ): List[(Pre, Pre)] = {
      from map (case_(_, ctx, scope))
    }

    def leteq(from: Expr, ctx: Set[Name], scope: Map[Name, Type]): (Var, Pre) =
      from match {
        case App(Id(name), what) =>
          leteq(name, expr(what, ctx, scope))
        case _ =>
          error("invalid let binding: " + from)
      }

    def leteqs(
        from: List[Expr],
        ctx: Set[Name],
        scope: Map[Name, Type]
    ): List[(Var, Pre)] = {
      from map (leteq(_, ctx, scope))
    }

    def exprs(
        from: List[Expr],
        ctx: Set[Name],
        scope: Map[Name, Type]
    ): List[Pre] = {
      from map (expr(_, ctx, scope))
    }
  }
}

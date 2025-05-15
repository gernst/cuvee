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
import cuvee.imp.Prog
import cuvee.imp.Spec
import cuvee.imp.Return
import cuvee.imp.Break
import cuvee.imp.Continue
import cuvee.imp.While
import cuvee.imp.If
import cuvee.imp.Skip
import cuvee.imp.Block
import cuvee.imp.Local
import cuvee.ai.domain.AInts.local

object Parser {
  def ack(from: Expr): Ack =
    from match {
      case Id("success") =>
        Success
      case Id("unsupported") =>
        Unsupported
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

  def labels(from: Expr): Labels =
    from match {
      case App(Id("labels"), ids @ _*) =>
        Labels(ids.toList map { case Id(name) => name })
      case App(Id("error"), args @ _*) =>
        Error(args.toList)
      case _ =>
        error("invalid label: " + from)
    }
}

class Parser(init: State) {
  // import st._
  var stack = List(init)
  def st = stack.head

  val int = st.sort("Int")
  val bool = st.sort("Bool")
  val real = st.sort("Real")

  val ctx0: Set[Name] = Set()

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

      case App(Id("push")) =>
        val n = 1
        stack = List.tabulate(n)(_ => stack.head) ++ stack
        Push(n)

      case App(Id("pop")) =>
        val n = 1
        stack = stack drop n
        Pop(n)

      case App(Id("reset")) =>
        stack = List(init)
        Reset

      case App(Id("exit")) =>
        Exit

      case App(Id("assert"), phi) =>
        val phi_ = expr_typed(phi, bool)
        Assert(phi_)

      // these are extensions to SMT-LIB
      case App(Id("lemma"), phi) =>
        val phi_ = expr_typed(phi, bool)
        Lemma(phi_, None, None, Nil)

      // case App(Id("free-lemma"), phi) =>
      //   val phi_ = expr_typed(phi, bool)
      //   Lemma(phi_, None, Some(Free))

      // prove is used in TIP https://github.com/tip-org/
      case App(Id("prove"), phi) =>
        val phi_ = expr_typed(phi, bool)
        Lemma(phi_, None, Some(Goal), Nil)

      case App(Id("declare-sort"), Id(name), Lit.num(digits)) =>
        val n = digits.toInt
        st.con(name, n)
        DeclareSort(name, n)

      case App(Id("define-sort"), Id(name), App(args @ _*), res) =>
        val params_ = params(args.toList)
        val n = params_.length
        val ctx = params_.names.toSet
        val res_ = typ(res, ctx)
        st.con(name, n)
        st.condef(name, params_, res_)
        DefineSort(name, params_, res_)

      case App(Id("declare-var"), Id(name), res) =>
        val res_ = typ(res)
        DeclareVar(name, res_)

      case App(Id("declare-const"), Id(name), res) =>
        val args_ = Nil
        val res_ = typ(res)
        st.fun(name, Nil, args_, res_)
        DeclareFun(name, Nil, args_, res_)

      case App(Id("declare-fun"), Id(name), App(args @ _*), res) =>
        val args_ = types(args.toList)
        val res_ = typ(res)
        st.fun(name, Nil, args_, res_)
        DeclareFun(name, Nil, args_, res_)

      case App(Id("declare-fun"), Id(name), App(Id("par"), App(gen @ _*), App(args @ _*), res)) =>
        val params_ = params(gen.toList)
        val ctx = params_.names.toSet
        val args_ = types(args.toList, ctx)
        val res_ = typ(res, ctx)
        st.fun(name, params_, args_, res_)
        DeclareFun(name, params_, args_, res_)

      case App(Id(cmd), Id(name), App(args @ _*), res, body)
          if cmd == "define-fun" || cmd == "define-fun-rec" =>
        val formals_ = formals(args.toList)
        val res_ = typ(res)
        st.fun(name, Nil, formals_.types, res_)

        val body_ = expr_typed(body, res_, ctx0, formals_.pairs)
        st.fundef(name, formals_, body_)

        DefineFun(name, Nil, formals_, res_, body_, cmd == "define-fun-rec")

      case App(Id(cmd), Id(name), App(Id("par"), App(gen @ _*), App(args @ _*), res, body))
          if cmd == "define-fun" || cmd == "define-fun-rec" =>
        val params_ = params(gen.toList)
        val ctx = params_.names.toSet
        val formals_ = formals(args.toList, ctx)
        val res_ = typ(res, ctx)
        st.fun(name, params_, formals_.types, res_)

        val body_ = expr_typed(body, res_, ctx, formals_.pairs)
        st.fundef(name, formals_, body_)

        DefineFun(name, Nil, formals_, res_, body_, cmd == "define-fun-rec")

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

      // benchmarks-dtt format
      case App(Id("declare-datatypes"), App(), App(froms @ _*)) =>
        val stuff = froms map { case App(Id(name), constrs @ _*) =>
          ((Name(name), 0), App(constrs: _*))
        }

        val (decls, froms_) = stuff.unzip
        val dts = datatypes(decls.toList, froms_.toList)
        DeclareDatatypes(decls.toList, dts)

      case App(Id("declare-datatypes"), App(names @ _*), App(froms @ _*)) =>
        val decls = arities(names.toList)
        require(decls.length == froms.length, "invalid datatype specification: " + from)
        val dts = datatypes(decls, froms.toList)
        DeclareDatatypes(decls, dts)

      case App(Id("declare-abstractions"), App(names @ _*), App(froms @ _*)) =>
        val decls = arities(names.toList)
        require(decls.length == froms.length, "invalid datatype specification: " + from)
        val dts = datatypes(decls, froms.toList)
        DeclareAbstractions(decls, dts)

      case App(Id("declare-contract"), Id(name), App(formals @ _*), App(contracts @ _*)) =>
        // once we know we parse contracts, add some stuff to the state
        val params_ : List[Param] = Nil

        val formals_ = formals_with_mode(formals.toList)
        val scope = formals_ map { case (_, cuvee.pure.Var(name, t)) => name -> t }
        val contracts_ = expr_pairs_typed(contracts.toList, (bool, bool), params_.names, scope)

        st.contract(name, params_, formals_, contracts_)
        DeclareContracts(name, params_, formals_, contracts_)

      case App(Id("define-proc"), Id(name), App(in @ _*), App(out @ _*), App(locals @ _*), body) =>
        val params_ : List[Param] = Nil
        // val params_ = params(gen.toList)
        val ctx = params_.names.toSet

        val in_ = formals(in.toList, ctx)
        val out_ = formals(out.toList, ctx)
        val locals_ = formals(locals.toList, ctx)
        val formals_ = in_ ++ out_ ++ locals_
        val scope = formals_.pairs

        val body_ = prog(body, ctx, scope.toMap)
        val body_with_locals_ = Block(List(Local(locals_, Nil), body_))

        st.proc(name, params_, in_, out_, None)
        DefineProc(name, params_, in_, out_, None, body_with_locals_)

      case App(Id("define-proc"), Id(name), App(in @ _*), App(out @ _*), body) =>
        val params_ : List[Param] = Nil
        // val params_ = params(gen.toList)
        val ctx = params_.names.toSet

        val in_ = formals(in.toList, ctx)
        val out_ = formals(out.toList, ctx)
        val formals_ = in_ ++ out_
        val scope = formals_.pairs

        val body_ = prog(body, ctx, scope.toMap)

        st.proc(name, params_, in_, out_, None)
        DefineProc(name, params_, in_, out_, None, body_)

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
      yield {
        val dt = datatype(name, arity, from)
        st.datatype(name, dt)
        dt
      }
  }

  def abstractions(
      decls: List[(Name, Int)],
      froms: List[Expr]
  ): List[Datatype] = {
    for (((name, arity), from) <- decls zip froms)
      st.con(name, arity)

    for (((name, arity), from) <- decls zip froms)
      yield {
        val dt = datatype(name, arity, from)
        st.abstraction(name, dt)
        dt
      }
  }

  def sel(params: List[Param], in: Sort, from: Expr, ctx: Set[Name]): Fun =
    from match {
      case App(Id(name), arg) =>
        val out = typ(arg, ctx)
        st.fun(name, params, List(in), out)

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

  def formal_with_mode(from: Expr, ctx: Set[Name] = Set()): (cuvee.imp.Mode, Var) =
    from match {
      case App(Id(name), App(Id("in"), what)) =>
        (cuvee.imp.Mode.In, Var(name, typ(what, ctx)))
      case App(Id(name), App(Id("out"), what)) =>
        (cuvee.imp.Mode.Out, Var(name, typ(what, ctx)))
      case App(Id(name), App(Id("inout"), what)) =>
        (cuvee.imp.Mode.InOut, Var(name, typ(what, ctx)))
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
        st.typ(name)
      case App(Id(name), args @ _*) =>
        st.typ(name, types(args.toList, ctx))
      case _ =>
        error("invalid type: " + from)
    }

  def cmds(from: List[Expr]): List[Cmd] =
    from map cmd

  def goals(from: Expr, ctx: Iterable[Name] = Set(), scope: Iterable[(Name, Type)] = Map()) =
    from match {
      case App(Id("goals"), args @ _*) =>
        val inner = exprs(st)

        args.toList flatMap {
          case App(Id("goal"), Kw(_), rest @ _*) =>
            Nil

          case App(Id("goal"), from, rest @ _*) =>
            val pre = inner.expr(from, ctx.toSet, scope.toMap)
            List(pre.resolve)

          case _ =>
            error("unexpected format in goal response: " + from)
        }

      case _ =>
        error("unexpected format in goals response: " + from)
    }

  def model(from: Expr): List[DefineFun] =
    from match {
      case App(defs @ _*) =>
        for (App(Id("define-fun"), Id(name), App(args @ _*), res, body) <- defs.toList) yield {
          val formals_ = formals(args.toList)
          val res_ = typ(res)
          val body_ = expr_typed(body, res_, ctx0, formals_.pairs)
          DefineFun(name, Nil, formals_, res_, body_, false)
        }

      case _ =>
        error("unexpected format in model response: " + from)
    }

  def formals(from: List[Expr], ctx: Set[Name] = Set()): List[Var] =
    from map (formal(_, ctx))

  def formals_with_mode(from: List[Expr], ctx: Set[Name] = Set()): List[(cuvee.imp.Mode, Var)] =
    from map (formal_with_mode(_, ctx))

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

  def expr_pairs_typed(
      from: List[Expr],
      expect: (Type, Type),
      ctx: Iterable[Name] = Set(),
      scope: Iterable[(Name, Type)] = Map()
  ) = from map {
    case App(e1, e2) =>
      val (t1, t2) = expect
      val inner = exprs(st)
      val pre = inner.expr(e1, ctx.toSet, scope.toMap)
      val post = inner.expr(e2, ctx.toSet, scope.toMap)
      inner.check(pre, t1)
      inner.check(post, t2)
      (pre.resolve, post.resolve)

    case arg =>
      cuvee.error("expected pair of expressions: " + arg)
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

  def attrs(from: List[Expr]): List[(Kw, Option[Expr])] =
    from match {
      case Nil =>
        Nil

      case (kw: Kw) :: (rest @ ((_: Kw) :: _)) =>
        (kw -> None) :: attrs(rest)

      case (kw: Kw) :: arg :: rest =>
        (kw -> Some(arg)) :: attrs(rest)

      case _ =>
        cuvee.error("invalid attributes: " + from)
    }

  def prog(
      from: Expr,
      ctx: Set[Name],
      scope: Map[Name, Type]
  ): Prog = from match {
    case App(Id("return"))   => Return
    case App(Id("break"))    => Break
    case App(Id("continue")) => Continue

    case App(Id("assume"), phi) =>
      val phi_ = expr_typed(phi, bool, ctx, scope)
      Spec.assume(phi_)

    case App(Id("assert"), phi) =>
      val phi_ = expr_typed(phi, bool, ctx, scope)
      Spec.assert(phi_)

    case App(Id("havoc"), App(xs @ _*)) =>
      val xs_ = xs.toList map { case Id(name) => Var(name, scope(name)) }
      Spec.havoc(xs_)

    case App(Id("sequence"), progs @ _*) =>
      val progs_ = progs.toList map (prog(_, ctx, scope))
      Block(progs_)

    case App(Id("if"), test, left) =>
      val test_ = expr_typed(test, bool, ctx, scope)
      val left_ = prog(left, ctx, scope)
      val right_ = Skip
      If(test_, left_, right_)

    case App(Id("if"), test, left, right) =>
      val test_ = expr_typed(test, bool, ctx, scope)
      val left_ = prog(left, ctx, scope)
      val right_ = prog(right, ctx, scope)
      If(test_, left_, right_)

    case App(Id("while"), test, body) =>
      val test_ = expr_typed(test, bool, ctx, scope)
      val body_ = prog(body, ctx, scope)
      While(test_, body_)

    case App(Id("!"), from, rest @ _*) =>
      cuvee.imp.Note(prog(from, ctx, scope), attrs(rest.toList))

    case _ =>
      cuvee.error("unexpected program: " + from)
  }

  def exprs(st: State) = new st.Exprs {
    def expr(from: Expr, ctx: Set[Name], scope: Map[Name, Type]): Pre =
      from match {
        case Lit.num(digits) =>
          lit(BigInt(digits), int)

        case Lit.dec(digits) =>
          lit(digits.toDouble, real)

        case Id(name) if scope contains name =>
          x(name, scope(name))

        case Id(name) if st.funs contains (name, 0) =>
          const(name)

        case App(Id("!"), from, rest @ _*) =>
          note(expr(from, ctx, scope), attrs(rest.toList))

        case App(Id("distinct"), rest @ _*) =>
          distinct(exprs(rest.toList, ctx, scope))

        case App(Id("+"), rest @ _*) =>
          commutative("+", lit(BigInt(0), Sort.int), exprs(rest.toList, ctx, scope))

        case App(Id("*"), rest @ _*) =>
          commutative("*", lit(BigInt(1), Sort.int), exprs(rest.toList, ctx, scope))

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

        case App(App(Id("_"), Id("is"), Id(name)), arg) =>
          st.constr(name) match {
            case Some(fun) =>
              is(expr(arg, ctx, scope), fun)
            case None =>
              error("invalid constructor: " + name)
          }

        // qualified constant
        case App(Id("as"), Id(name), from) if st.funs contains (name, 0) =>
          const(name, Some(typ(from, ctx)))

        // qualified function application
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
          ??? // need to make function generic!
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
          error("invalid match case: " + from)
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

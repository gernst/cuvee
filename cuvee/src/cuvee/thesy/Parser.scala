package cuvee.thesy

import cuvee.State
import cuvee.util.Name
import cuvee.pure.Rule
import cuvee.pure.Param
import cuvee.pure.Type
import cuvee.smtlib._
import cuvee.pure.Datatype
import cuvee.pure.Sort
import cuvee.pure.Fun
import cuvee.error
import cuvee.pure.Var
import cuvee.trace

class Parser(val st: State) {
  import cuvee.sexpr._

  val ctx0: Set[Name] = Set()

  st.con("Nat", 0)
  val nat = st.sort("Nat")
  val bool = st.sort("Bool")
  st.fun("less", Nil, List(nat, nat), bool)

  def cmds(from: List[Expr]): List[Cmd] =
    from map cmd

  def cmd(from: Expr): Cmd = from match {
    case App(Id("datatype"), Id(name), App(ps @ _*), App(cs @ _*)) =>
      val params_ = params(ps.toList)
      val arity = params_.length
      st.con(name, arity)
      val res_ = st.sort(name, params_)
      val dt = Datatype(params_, constrs(name, params_, res_, cs.toList, ctx0))
      st.datatype(name, dt)
      DeclareDatatypes(List((name, arity)), List(dt))

    case App(Id("declare-fun"), Id(name), App(args @ _*), res) =>
      val args_ = types(args.toList)
      val res_ = typ(res)
      st.fun(name, Nil, args_, res_)
      DeclareFun(name, Nil, args_, res_)

    case App(Id("=>"), Id(_), lhs, rhs) =>
      val eq = exprs.rule(lhs, rhs)
      Assert(eq.toExpr)

    case App(Id("prove"), from) =>
      val phi = exprs.expr(from, Map())
      Lemma(phi.resolve, None, true)

    case _ =>
      error("invalid command: " + from)
  }

  def formals(from: List[Expr], ctx: Set[Name] = Set()): List[Var] =
    from map (formal(_, ctx))

  def formal(from: Expr, ctx: Set[Name] = Set()): Var =
    from match {
      case App(Id(name), what) =>
        Var(name, typ(what, ctx))
      case _ =>
        error("invalid formal parameter: " + from)
    }

  def constr(
      name: String,
      params: List[Param],
      res: Sort,
      from: Expr,
      ctx: Set[Name]
  ): (Fun, List[Fun]) =
    from match {
      case App(Id(c), args @ _*) =>
        val types_ = types(args.toList.take(args.length - 1), ctx)
        val sels_ =
          for ((typ, i) <- types_.zipWithIndex)
            yield st.fun(Name(name + "_" + c + "_", Some(i)), params, List(typ), res)
        st.fun(c, params, types_, res) -> sels_

      case _ =>
        error("invalid constructor declaration: " + from)
    }

  def constrs(
      name: String,
      params: List[Param],
      res: Sort,
      from: List[Expr],
      ctx: Set[Name]
  ): List[(Fun, List[Fun])] =
    from map { constr(name, params, res, _, ctx) }

  def params(from: List[Expr]): List[Param] =
    from map param

  def param(from: Expr): Param =
    from match {
      case Id(name) =>
        Param(name)
      case _ =>
        error("invalid type parameter: " + from)
    }

  def rule(from: List[Expr]) = from match {
    case List(lhs, Id("=>"), rhs) =>
      exprs.rule(lhs, rhs)

    case _ =>
      cuvee.error("rule format not supported: " + from)
  }

  def types(from: List[Expr], ctx: Set[Name] = Set()): List[Type] =
    from map (typ(_, ctx))

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

  def exprs = new st.Exprs {
    var ctx = ctx0
    var scope: Map[String, Type] = Map()

    def rule(lhs: Expr, rhs: Expr) = {
      val lhs_ = expr(lhs, Map())
      val rhs_ = expr(rhs, Map())
      unify(lhs_.typ, rhs_.typ)
      Rule(lhs_.resolve, rhs_.resolve)
    }

    def expr(from: Expr, bound: Map[Name, Type]): Pre = from match {
      case Id(name) if name.startsWith("?") =>
        if (scope contains name) {
          x(name, scope(name))
        } else {
          val a = Param.fresh("a")
          scope = scope + (name -> a)
          x(name, a)
        }

      case Id(name) if bound contains name =>
        x(name, bound(name))

      case Id(name) =>
        const(name)

      case App(Id(name), App(vs @ _*), arg) if name == "exists" | name == "forall" =>
        val xs = formals(vs.toList, ctx)
        val body = expr(arg, bound ++ xs.pairs)
        check(body, bool)
        bind(name, xs, body, bool)

      case App(Id(name), args @ _*) =>
        app(name, args.toList map (expr(_, bound)))
    }
  }
}

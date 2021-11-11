package cuvee

object Cuvee {
  val univ: pure.Univ = ???
  val sig: pure.Sig = ???

  object translate extends sig.Exprs {
    import univ._

    val int = sort("Int")
    val real = sort("Real")
    val bool = sort("Bool")

    def array(dom: pure.Type, ran: pure.Type) =
      sort("Array", List(dom, ran))

    def formal(from: sexpr.Expr): (String, pure.Type) =
      from match {
        case sexpr.App(List(sexpr.Id(name), what)) =>
          (name, typ(what))
      }

    def typ(from: sexpr.Expr): pure.Type =
      from match {
        case sexpr.Id(name) =>
          sort(name)
        case sexpr.App(sexpr.Id(name) :: args) =>
          sort(name, types(args))
      }

    def expr(from: sexpr.Expr, scope: Map[String, pure.Type]): Pre =
      from match {
        case sexpr.Lit.num(digits) =>
          lit(digits.toInt, int)

        case sexpr.Lit.dec(digits) =>
          lit(digits.toDouble, real)

        case sexpr.Id(name) if scope contains name =>
          x(name, scope(name))

        case sexpr.Id(name) if sig.funs contains name =>
          const(name)

        case sexpr.App(sexpr.Id(name) :: args) if sig.funs contains name =>
          app(name, exprs(args, scope))

        case sexpr.App(List(sexpr.Id(name), sexpr.App(bound), arg))
            if name == "exists" | name == "forall" =>
          val xs = formals(bound)
          val body = expr(arg, scope ++ xs)
          check(body, bool)
          bind(name, xs, body, bool)

        case sexpr.App(List(sexpr.Id(name), sexpr.App(List(bound)), arg))
            if name == "lambda" =>
          val x @ (_, t) = formal(bound)
          val body = expr(arg, scope + x)
          bind(name, List(x), body, array(t, body.typ))
      }

    def formals(from: List[sexpr.Expr]): List[(String, pure.Type)] =
      from map formal

    def types(from: List[sexpr.Expr]): List[pure.Type] =
      from map typ

    def exprs(
        from: List[sexpr.Expr],
        scope: Map[String, pure.Type]
    ): List[Pre] = {
      from map (expr(_, scope))
    }
  }
}

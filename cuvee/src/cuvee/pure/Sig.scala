package cuvee.pure

object Sig {
  def apply(funs: (String, Fun)*): Sig = {
    Sig(funs.toMap)
  }

  def fun(
      name: String,
      params: List[Param],
      args: List[Type],
      res: Type
  ): Fun = {
    Fun(name, params, args, res)
  }
}

case class Sig(funs: Map[String, Fun]) {
  class Exprs {
    var su: Map[Param, Type] = Map()

    case class Pre(private[Exprs] val expr: Expr) {
      def resolve = expr inst su
    }

    def unify(typ1: Type, typ2: Type) {
      su = Type.unify(typ1, typ2, su)
    }

    def unify(types1: List[Type], types2: List[Type]) {
      su = Type.unify(types1, types2, su)
    }

    def x(name: String, typ: Type) = {
      Pre(Var(name, typ))
    }

    def lit(any: Any, typ: Type) = {
      Pre(Lit(any, typ))
    }

    def bind(
        name: String,
        bound: List[(String, Type)],
        body: Pre,
        typ: Type
    ) = {
      val quant = Quant(name)
      val xs =
        for ((name, typ) <- bound)
          yield Var(name, typ)
      check(body, typ)
      Pre(Bind(quant, xs, body.expr))
    }

    def const(name: String) = {
      app(name, Nil)
    }

    def app(name: String, args: List[Pre]) = {
      val fun = funs(name)
      val inst = fun.gen
      val exprs = args map (_.expr)
      unify(inst.args, exprs.typ)
      Pre(App(inst, exprs))
    }

    def check(arg: Pre, typ: Type) {
      unify(arg.expr.typ, typ)
    }
  }
}

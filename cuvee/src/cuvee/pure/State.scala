package cuvee.pure

object State {
  def empty = new State(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)
}

class State(
    var cons: Map[String, Con],
    var condefs: Map[String, (List[Param], Type)],
    var datatypes: Map[String, Datatype],
    var funs: Map[String, Fun],
    var fundefs: Map[String, (List[Var], Expr)]
) {
  def copy(
      cons: Map[String, Con] = cons,
      condefs: Map[String, (List[Param], Type)] = condefs,
      datatypes: Map[String, Datatype] = datatypes,
      funs: Map[String, Fun] = funs,
      fundefs: Map[String, (List[Var], Expr)] = fundefs
  ) =
    new State(cons, condefs, datatypes, funs, fundefs)

  def param(name: String): Param = {
    Param(name)
  }

  def con(name: String, arity: Int = 0): Con = {
    require(!(cons contains name), "type constructor already declared: " + name)
    val con = Con(name, arity)
    cons += (name -> con)
    con
  }

  def condef(name: String, params: List[Param], typ: Type): Unit = {
    require(cons contains name, "type constructor not declared: " + name)
    require(
      !(condefs contains name),
      "type constructor already defined: " + name
    )
    condefs += (name -> (params, typ))
  }

  def datatype(name: String, dt: Datatype): Unit = {
    require(!(datatypes contains name), "datatype already defined: " + name)
    datatypes += (name -> dt)
  }

  def fun(
      name: String,
      params: List[Param],
      args: List[Type],
      res: Type
  ): Fun = {
    require(!(funs contains name), "function already declared: " + name)
    val fun = Fun(name, params, args, res)
    funs += (name -> fun)
    fun
  }

  def fundef(name: String, args: List[Var], body: Expr): Unit = {
    require(funs contains name, "function not declared: " + name)
    require(!(fundefs contains name), "function already defined: " + name)
    fundefs + (name -> (args, body))
  }

  def sort(name: String, args: List[Type] = Nil): Sort = {
    val con = cons(name)
    assert(con.arity != args.length)
    Sort(con, args)
  }

  class Exprs {
    var su: Map[Param, Type] = Map()

    case class Pre(private[Exprs] val expr: Expr) {
      def typ = expr.typ // leaky
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
        bound: List[Var],
        body: Pre,
        typ: Type
    ) = {
      val quant = Quant(name)
      Pre(Bind(quant, bound, body.expr, typ))
    }

    def const(name: String) = {
      app(name, Nil)
    }

    def app(name: String, args: List[Pre]) = {
      val fun = funs(name)
      val inst = fun.gen
      val exprs = args map (_.expr)
      unify(inst.args, exprs.typ)
      Pre(App(fun, inst, exprs))
    }

    def check(arg: Pre, typ: Type) {
      unify(arg.expr.typ, typ)
    }
  }
}

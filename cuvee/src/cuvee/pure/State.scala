package cuvee.pure

import cuvee.trace

object State {
  def empty = new State(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)

  def default = {
    val st = empty

    st.con("Int")
    st.con("Bool")
    st.con("Real")

    // st.con("List", 1)
    st.con("Array", 2)

    val Int = st.sort("Int")
    val Bool = st.sort("Bool")
    val a = st.param("a")
    val b = st.param("b")

    // def list(elem: Type) = st.sort("List", List(elem))
    def array(dom: Type, ran: Type) = st.sort("Array", List(dom, ran))

    st.fun("=", List(a), List(a, a), Bool)
    st.fun("ite", List(a), List(Bool, a, a), a)

    val ar = array(a, b)
    st.fun("select", List(a, b), List(ar, a), b)
    st.fun("store", List(a, b), List(ar, a, b), ar)

    st.fun("true", Nil, Nil, Bool)
    st.fun("false", Nil, Nil, Bool)
    st.fun("not", Nil, List(Bool), Bool)
    st.fun("and", Nil, List(Bool, Bool), Bool)
    st.fun("or", Nil, List(Bool, Bool), Bool)
    st.fun("=>", Nil, List(Bool, Bool), Bool)

    st.fun("-", Nil, List(Int), Int)

    st.fun("+", Nil, List(Int, Int), Int)
    st.fun("-", Nil, List(Int, Int), Int)
    st.fun("*", Nil, List(Int, Int), Int)

    st.fun("<=", Nil, List(Int, Int), Bool)
    st.fun(">=", Nil, List(Int, Int), Bool)
    st.fun("<", Nil, List(Int, Int), Bool)
    st.fun(">", Nil, List(Int, Int), Bool)

    st
  }
}

class State(
    var cons: Map[String, Con],
    var condefs: Map[String, (List[Param], Type)],
    var datatypes: Map[String, Datatype],
    var funs: Map[(String, Int), Fun],
    var fundefs: Map[(String, Int), (List[Var], Expr)]
) {
  def constrs =
    for (
      (_, dt) <- datatypes.toSet;
      (c, _) <- dt.constrs
    )
      yield c

  def copy(
      cons: Map[String, Con] = cons,
      condefs: Map[String, (List[Param], Type)] = condefs,
      datatypes: Map[String, Datatype] = datatypes,
      funs: Map[(String, Int), Fun] = funs,
      fundefs: Map[(String, Int), (List[Var], Expr)] = fundefs
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
    val arity = args.length
    require(!(funs contains (name, arity)), "function already declared: " + name)
    val fun = Fun(name, params, args, res)
    funs += ((name, arity) -> fun)
    fun
  }

  def fundef(name: String, args: List[Var], body: Expr): Unit = {
    val arity = args.length
    require(funs contains (name, arity) , "function not declared: " + name)
    require(!(fundefs contains (name, arity)), "function already defined: " + name)
    fundefs + ((name, arity) -> (args, body))
  }

  def sort(name: String, args: List[Type] = Nil): Sort = {
    require(cons contains name, "type constructor not declared: " + name)
    val con = cons(name)
    require(
      con.arity == args.length,
      "arity mismatch: " + con + " and args: " + args
    )
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
      val arity = args.length
      val fun = funs(name, arity)
      val inst = fun.generic
      val exprs = args map (_.expr)
      cuvee.trace("cannot apply " + fun + " to " + args) {
        unify(inst.args, exprs.types)
      }
      Pre(App(inst, exprs))
    }

    def match_(arg: Pre, cases: List[(Pre, Pre)]) = {
      val typ = Type.fresh(Param("a"))
      val expr = arg.expr
      val body =
        for ((pat, res) <- cases)
          yield {
            check(pat, expr.typ)
            check(res, typ)
            Case(pat.expr, res.expr)
          }
      Pre(Match(expr, body, typ))
    }

    def in(k: Int, arg: Pre, typ: Type) = {
      Pre(In(k, arg.expr, typ))
    }

    def tuple(args: List[Pre]) = {
      val exprs = args map (_.expr)
      Pre(Tuple(exprs))
    }

    def check(arg: Pre, typ: Type) {
      trace("checking\n  " + arg.expr + ":\n    " + typ) {
        unify(arg.expr.typ, typ)
      }
    }
  }
}

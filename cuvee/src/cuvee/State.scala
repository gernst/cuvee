package cuvee

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._

object State {
  def empty =
    new State(
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty
    )

  def default = {
    val st = empty

    st.con("Bool")
    st.con("Int")
    st.con("Real")

    st.con("RoundingMode")

    // st.con("List", 1)
    st.con("Array", 2)

    val Bool = st.sort("Bool")
    val Int = st.sort("Int")
    val Real = st.sort("Real")

    val a = st.param("a")
    val b = st.param("b")

    // def list(elem: Type) = st.sort("List", List(elem))
    def array(dom: Type, ran: Type) = st.sort("Array", List(dom, ran))

    st.fun("undefined", List(a), Nil, a)
    st.fun("to_int", Nil, List(Real), Int)
    st.fun("to_real", Nil, List(Int), Real)

    st.fun("=", List(a), List(a, a), Bool)
    st.fun("ite", List(a), List(Bool, a, a), a)

    val ar = array(a, b)
    st.fun("const", List(a, b), List(b), ar)
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
    st.fun("div", Nil, List(Int, Int), Int)
    st.fun("mod", Nil, List(Int, Int), Int)

    st.fun("<=", Nil, List(Int, Int), Bool)
    st.fun(">=", Nil, List(Int, Int), Bool)
    st.fun("<", Nil, List(Int, Int), Bool)
    st.fun(">", Nil, List(Int, Int), Bool)

    st
  }
}

class State(
    var cons: Map[Name, Con],
    var condefs: Map[Name, (List[Param], Type)],
    var datatypes: Map[Name, Datatype],
    var funs: Map[(Name, Int), Fun],
    var fundefs: Map[(Name, Int), (List[Var], Expr)],
    var procs: Map[Name, Proc],
    var procdefs: Map[Name, (List[Var], List[Var], Prog)]
) {
  def constrs =
    for (
      (_, dt) <- datatypes.toSet;
      (c, _) <- dt.constrs
    )
      yield c

  def copy(
      cons: Map[Name, Con] = cons,
      condefs: Map[Name, (List[Param], Type)] = condefs,
      datatypes: Map[Name, Datatype] = datatypes,
      funs: Map[(Name, Int), Fun] = funs,
      fundefs: Map[(Name, Int), (List[Var], Expr)] = fundefs,
      procs: Map[Name, Proc] = procs,
      procdefs: Map[Name, (List[Var], List[Var], Prog)] = procdefs
  ) =
    new State(cons, condefs, datatypes, funs, fundefs, procs, procdefs)

  def param(name: Name): Param = {
    Param(name)
  }

  def con(name: Name, arity: Int = 0): Con = {
    val con = Con(name, arity)
    if (cons contains name)
      require(cons(name) == con, "type constructor already declared: " + name)
    cons += (name -> con)
    con
  }

  def condef(name: Name, params: List[Param], typ: Type): Unit = {
    require(cons contains name, "type constructor not declared: " + name)
    if (condefs contains name)
      require(
        condefs(name) == (params, typ),
        "type constructor already defined: " + name
      )
    condefs += (name -> (params, typ))
  }

  def datatype(name: Name, dt: Datatype): Unit = {
    require(cons contains name, "type constructor not declared: " + name)
    if (datatypes contains name)
      require(datatypes(name) == dt, "datatype already defined: " + name)
    datatypes += (name -> dt)
  }

  def fun(
      name: Name,
      params: List[Param],
      args: List[Type],
      res: Type
  ): Fun = {
    val arity = args.length
    val fun = Fun(name, params, args, res)
    if (funs contains (name, arity))
      require(funs(name, arity) == fun, "function already declared: " + name)
    funs += ((name, arity) -> fun)
    fun
  }

  def fundef(name: Name, args: List[Var], body: Expr): Unit = {
    val arity = args.length
    require(funs contains (name, arity), "function not declared: " + name)
    if (fundefs contains (name, arity))
      require(fundefs(name, arity) == (args, body), "function already defined")
    fundefs += ((name, arity) -> (args, body))
  }

  def proc(
      name: Name,
      params: List[Param],
      in: List[Var],
      out: List[Var],
      spec: Option[Spec]
  ): Proc = {
    // require(
    //   !(procs contains name),
    //   "procedure already declared: " + name
    // )
    val proc = Proc(name, params, in, out, spec)
    procs += (name -> proc)
    proc
  }

  def procdef(name: Name, in: List[Var], out: List[Var], body: Prog): Unit = {
    // require(
    //   !(procdefs contains name),
    //   "procedure already defined: " + name
    // )
    procdefs += (name -> (in, out, body))
  }

  def sort(name: Name, args: List[Type] = Nil): Sort = {
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

    def x(name: Name, typ: Type) = {
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

    def leteq(name: Name, arg: Pre) = {
      val x = Var(name, Param.fresh("a"))
      (x, arg)
    }

    def let(
        eqs: List[(Var, Pre)],
        body: Pre
    ) = {
      val vars = eqs map (_._1)
      val args = eqs map (_._2.expr)
      unify(vars.types, args.types)
      val eqs_ =
        for ((x, e) <- (vars zip args))
          yield LetEq(x, e)
      Pre(Let(eqs_, body.expr))
    }

    def const(name: Name) = {
      app(name, Nil)
    }

    def select(base: Pre, index: Pre) = {
      app("select", List(base, index))
    }

    def store(base: Pre, index: Pre, value: Pre) = {
      app("store", List(base, index, value))
    }

    def ite(test: Pre, left: Pre, right: Pre) = {
      app("ite", List(test, left, right))
    }

    def note(expr: Pre, attr: List[sexpr.Expr]) = {
      Pre(Note(expr.expr, attr))
    }

    def app(name: Name, args: List[Pre], res: Option[Type] = None) = {
      val arity = args.length
      val fun = funs(name, arity)
      val inst = fun.generic
      val exprs = args map (_.expr)

      cuvee.trace("cannot apply " + fun + " to " + args) {
        unify(inst.args, exprs.types)
      }

      for (typ <- res) {
        cuvee.trace("cannot cast " + fun + " to " + typ) {
          unify(inst.res, typ)
        }
      }

      Pre(App(inst, exprs))
    }

    def match_(arg: Pre, cases: List[(Pre, Pre)]) = {
      val typ = Param.fresh("a")
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

    def distinct(args: List[Pre]) = {
      val exprs = args map (_.expr)
      Pre(Distinct(exprs))
    }

    def check(arg: Pre, typ: Type) {
      trace("checking\n  " + arg.expr + ":\n    " + typ) {
        unify(arg.expr.typ, typ)
      }
    }
  }
}

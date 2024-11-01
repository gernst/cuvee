package cuvee

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._
import cuvee.smtlib._

object State {
  def empty =
    new State(
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty
    )

  def default =
    empty.withDefault

  // contruct state from scatch, given a list of commands
  def apply(cmds: List[Cmd]): State = {
    default.added(cmds)
  }
}

class State(
    var cons: Map[Name, Con],
    var condefs: Map[Name, (List[Param], Type)],
    var datatypes: Map[Name, Datatype],
    var vars: Map[Name, Var],
    var funs: Map[(Name, Int), Fun],
    var fundefs: Map[(Name, Int), (List[Var], Expr)],
    var procs: Map[Name, Proc],
    var procdefs: Map[Name, (List[Var], List[Var], Prog)],
    var contracts: Map[Name, Contracts]
) {
  def constr(name: Name) =
    constrs.find(_.name == name)

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
      vars: Map[Name, Var] = vars,
      funs: Map[(Name, Int), Fun] = funs,
      fundefs: Map[(Name, Int), (List[Var], Expr)] = fundefs,
      procs: Map[Name, Proc] = procs,
      procdefs: Map[Name, (List[Var], List[Var], Prog)] = procdefs,
      contracts: Map[Name, Contracts] = contracts
  ) = {
    new State(cons, condefs, datatypes, vars, funs, fundefs, procs, procdefs, contracts)
  }

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

    for ((constr, sels) <- dt.constrs) {
      require(
        funs contains (constr.name, constr.arity),
        "constructor not previously declared: " + constr.name
      )

      for (sel <- sels)
        require(
          funs contains (sel.name, sel.arity),
          "selector not previously declared: " + sel.name + " of constructor " + constr.name
        )
    }

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

  def fundef(name: Name, formals: List[Var], body: Expr): Unit = {
    val arity = formals.length
    require(funs contains (name, arity), "function not declared: " + name)
    if (fundefs contains (name, arity))
      require(fundefs(name, arity) == (formals, body), "function already defined")
    fundefs += ((name, arity) -> (formals, body))
  }

  def proc(
      name: Name,
      params: List[Param],
      in: List[Var],
      out: List[Var],
      spec: Option[Spec]
  ): Proc = {
    require(
      !(procs contains name),
      "procedure already declared: " + name
    )
    val proc = Proc(name, params, in, out, spec)
    procs += (name -> proc)
    proc
  }

  def procdef(name: Name, in: List[Var], out: List[Var], body: Prog): Unit = {
    require(
      !(procdefs contains name),
      "procedure already defined: " + name
    )
    procdefs += (name -> (in, out, body))
  }

  def contract(
      name: Name,
      params: List[Param],
      formals: List[(cuvee.imp.Mode, Var)],
      pairs: List[(Expr, Expr)]
  ): Contracts = {
    require(
      !(contracts contains name),
      "contract already declared: " + name
    )

    val entry = Contracts(name, params, formals, pairs)
    contracts += (name -> entry)
    entry
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

  def global(name: Name, typ: Type): Var = {
    require(!(vars contains name), "global variable already declared: " + name)
    val x = Var(name, typ)
    vars = vars + (name -> x)
    x
  }

  def typ(name: Name, args: List[Type] = Nil): Type = {
    if (condefs contains name) {
      val (params, typ) = condefs(name)
      val su = Type.subst(params, args)
      typ subst su
    } else {
      sort(name, args)
    }
  }

  class Exprs {
    var su: Map[Param, Type] = Map()

    case class Pre(private[Exprs] val expr: Expr) {
      def typ = expr.typ // leaky, used for lambdas

      def resolve = {
        val su_ = Type.prune(su)
        trace("resolving " + expr + " with " + su) {
          expr inst su_
        }
      }
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

    def is(arg: Pre, fun: Fun) = {
      Pre(Is(arg.expr, fun))
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

    def const(name: Name, res: Option[Type] = None) = {
      app(name, Nil, res)
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

    def note(expr: Pre, attr: List[(sexpr.Kw, Option[sexpr.Expr])]) = {
      Pre(Note(expr.expr, attr))
    }

    def commutative(fun: Name, neutral: Pre, args: List[Pre]): Pre = args match {
      case Nil       => neutral
      case List(arg) => arg
      case _ =>
        args reduce { (a, b) =>
          app(fun, List(a, b))
        }
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

      // bypass type check
      Pre(new App(inst, exprs))
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

  def add(cmds: List[Cmd]) {
    for (cmd <- cmds)
      add(cmd)
  }

  def added(cmds: List[Cmd]) = {
    val st = copy()
    st.add(cmds)
    st
  }

  def add(cmd: Cmd) = cmd match {
    case DeclareSort(name, arity) =>
      con(name, arity)
    case DefineSort(name, params, body) =>
      con(name, params.length)
      condef(name, params, body)

    case DeclareFun(name, params, args, res) =>
      fun(name, params, args, res)

    case DefineFun(name, params, formals, res, body, rec) =>
      fun(name, params, formals.types, res)
      fundef(name, formals, body)

    case DeclareDatatypes(arities, dts) =>
      for ((name, arity) <- arities)
        con(name, arity)

      for (((name, _), dt) <- arities zip dts) {
        for ((constr, sels) <- dt.constrs) {
          val Fun(name, params, args, res) = constr
          fun(name, params, args, res)

          for (sel <- sels) {
            val Fun(name, params, args, res) = sel
            fun(name, params, args, res)
          }
        }

        datatype(name, dt)
      }

    case DeclareProc(name, params, in, out, spec) =>
      proc(name, params, in, out, spec)
    case DefineProc(name, params, in, out, spec, body) =>
      proc(name, params, in, out, spec)
      procdef(name, in, out, body)

    case _ =>
  }

  def withDefault = {
    con("Bool")
    con("Int")
    con("Real")

    con("RoundingMode")

    // con("List", 1)
    con("Array", 2)

    val Bool = sort("Bool")
    val Int = sort("Int")
    val Real = sort("Real")

    val a = param("a")
    val b = param("b")

    // def list(elem: Type) = sort("List", List(elem))
    def array(dom: Type, ran: Type) = sort("Array", List(dom, ran))

    // fun("undefined", List(a), Nil, a)
    fun("to_int", Nil, List(Real), Int)
    fun("to_real", Nil, List(Int), Real)

    fun("=", List(a), List(a, a), Bool)
    fun("ite", List(a), List(Bool, a, a), a)

    val ar = array(a, b)
    fun("const", List(a, b), List(b), ar)
    fun("select", List(a, b), List(ar, a), b)
    fun("store", List(a, b), List(ar, a, b), ar)

    fun("true", Nil, Nil, Bool)
    fun("false", Nil, Nil, Bool)
    fun("not", Nil, List(Bool), Bool)
    fun("and", Nil, List(Bool, Bool), Bool)
    fun("or", Nil, List(Bool, Bool), Bool)
    fun("=>", Nil, List(Bool, Bool), Bool)

    fun("-", Nil, List(Int), Int)

    fun("+", Nil, List(Int, Int), Int)
    fun("-", Nil, List(Int, Int), Int)
    fun("*", Nil, List(Int, Int), Int)
    fun("div", Nil, List(Int, Int), Int)
    fun("mod", Nil, List(Int, Int), Int)

    fun("<=", Nil, List(Int, Int), Bool)
    fun(">=", Nil, List(Int, Int), Bool)
    fun("<", Nil, List(Int, Int), Bool)
    fun(">", Nil, List(Int, Int), Bool)

    this
  }

  def withContractLib = {
    val a = Param("a")
    val b = Param("b")

    fun("old", List(a), List(a), a)

    con("Set", 1)
    con("Seq", 1)
    con("Map", 2)

    val Bool = sort("Bool", Nil)
    val Int = sort("Int", Nil)
    val Set = sort("Set", List(a))
    val Seq = sort("Seq", List(a))
    val Map = sort("Map", List(a, b))

    fun("seq.empty", List(a), List(), Seq)
    fun("seq.len", List(a), List(Seq), Int)
    fun("seq.contains", List(a), List(Seq, Seq), Bool)
    fun("seq.unit", List(a), List(a), Seq)
    fun("seq.++", List(a), List(Seq, Seq), Seq)
    fun("seq.nth", List(a), List(Seq, Int), a)
    fun("seq.at", List(a), List(Seq, Int), Seq)
    fun("seq.update", List(a), List(Seq, Int, Seq), Seq)
    fun("seq.extract", List(a), List(Seq, Int, Int), Seq)

    this
  }
}

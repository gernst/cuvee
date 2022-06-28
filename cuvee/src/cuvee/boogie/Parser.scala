package cuvee.boogie

import arse._

import cuvee._
import cuvee.pure._
import cuvee.smtlib.Cmd
import cuvee.smtlib.Assert
import cuvee.smtlib.DeclareFun
import cuvee.smtlib.DefineFun
import cuvee.smtlib.DeclareSort
import cuvee.smtlib.DefineSort
import scala.util.DynamicVariable
import cuvee.smtlib.DeclareDatatypes

object Parser {
  import arse.implicits._

  // shadow existing definition for T = Token
  def ret[A](a: A) =
    new arse.Parser.Accept[A, Token](a)

  val la = just(op filter (_ == "<"))
  val ra = just(op filter (_ == ">"))

  def parens[A](p: Parser[A, Token]) = "(" ~ p ~ ")"
  def braces[A](p: Parser[A, Token]) = "{" ~ p ~ "}"
  def brackets[A](p: Parser[A, Token]) = "[" ~ p ~ "]"
  def angle[A](p: Parser[A, Token]) = la ~ p ~ ra

  def none[A](p: Parser[A, Token]) = p map { a => None }
  def some[A](p: Parser[A, Token]) = p map { a => Some(a) }

  object stack extends DynamicVariable(State.default) {
    def within[A](p: Parser[A, Token]) =
      S(p, this)
  }

  def state = stack.value

  object typing extends Scope[Param, Type] {
    def unify(typ1: Type, typ2: Type) = {
      value = Type.unify(typ1, typ2, value)
    }

    def unify(types1: List[Type], types2: List[Type]) = {
      value = Type.unify(types1, types2, value)
    }

    def app(name: Name, args: List[Expr]) = {
      val arity = args.length
      require(
        state.funs contains (name, arity),
        "no such function: " + (name, arity) + " in " + state.funs.keys
      )
      val fun = state funs (name, arity)
      val inst = fun.generic
      unify(inst.args, args.types)
      App(inst, args)
    }

    def bind(
        name: Name,
        bound: List[Var],
        body: Expr,
        typ: Type
    ) = {
      val quant = Quant(name.name)
      Bind(quant, bound, body, typ)
    }

    def checked(arg: Expr, typ: Type) = {
      trace("checking\n  " + arg + ":\n    " + typ) {
        unify(arg.typ, typ)
        arg inst value
      }
    }
  }

  def kw(name: String) = KW(name)
  val eof = new Token {}
  val id = V[String]
  val op = V[String]
  val number = V[String]
  val string = V[String]
  val quant = V[String]
  val name = P(Name(id))

  val con = P(state.cons(name))
  val gen = P(Param.from(name))
  val gens = P(angle(gen ~* ",") | ret(Nil))

  def make_sort(ctx: Map[Name, Param]): ((Name, List[Type]) => Type) = {
    case (name, Nil) if ctx contains name =>
      ctx(name)
    case (name, args) if state.cons contains name =>
      Sort(state.cons(name), args)
  }

  def typ(implicit ctx: Map[Name, Param]): Parser[Type, Token] =
    P(int | bool | real | array | sort)

  val int = P(Sort.int("int"))
  val bool = P(Sort.bool("bool"))
  val real = P(Sort.real("real"))

  def inst(implicit ctx: Map[Name, Param]) =
    P(angle(typ ~* ",") | ret(Nil))

  def sort(implicit ctx: Map[Name, Param]) =
    P(make_sort(ctx)(name ~ inst))

  def array(implicit ctx: Map[Name, Param]) =
    P(Sort.array(brackets(typ) ~ typ))

  val translate = Map(
    "<==>" -> "=",
    "==>" -> "=>",
    "&&" -> "and",
    "||" -> "or",
    "==" -> "=",
    "!=" -> "distinct",
    "/" -> "div",
    "%" -> "mod",
    "!" -> "not"
  )

  def make_op: ((String, List[Expr]) => Expr) = {
    case (name, args) if translate contains name =>
      val name_ = translate(name)
      typing.app(name_, args)

    case (name, args) =>
      typing.app(name, args)
  }

  def make_app(scope: Map[Name, Var]): ((Name, List[Expr]) => Expr) = {
    case (name, Nil) if scope contains name =>
      scope(name)
    case (name, args) if state.funs contains (name, args.length) =>
      typing.app(name, args)
    case (name, Nil) =>
      error("unknown variable or constant: " + name)
    case (name, _) =>
      error("unknown function: " + name)
  }

  def make_bind: ((String, (List[Var], Expr)) => Expr) = {
    case (name, (bound, body)) =>
      typing.bind(name, bound, body, Sort.bool)
  }

  def args(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(parens(expr ~* ",") | ret(Nil))

  def app(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_app(scope)(name ~ args))

  def expr(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Expr, Token] =
    M(inner, op, make_op, syntax)

  def scoped_expr(
      bound: List[Var]
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    expr(scope ++ bound.asScope, ctx)

  def inner(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Expr, Token] =
    P(parens(expr) | num | ite | bind | map | app)

  def make_int: (String => Expr) = { case text =>
    Lit(BigInt(text), Sort.int)
  }

  val num = P(make_int(number))

  def update(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(":=" ~ expr)
  def access(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(brackets(expr ~ update.?))

  val zip: ((Expr, List[(Expr, Option[Expr])]) => Expr) = {
    case (base, Nil) =>
      base
    case (base, (index, None) :: rest) =>
      zip(Select(base, index), rest)
    case (base, (index, Some(value)) :: rest) =>
      zip(Store(base, index, value), rest)
  }

  def map(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(zip(app ~ access.*))
  def ite(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

  def formal(implicit ctx: Map[Name, Param]) =
    P(Var(name ~ ":" ~ typ))
  def formals(implicit ctx: Map[Name, Param]) =
    P(formal ~* ",")

  def bind(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_bind(quant ~ (formals ~ "::" ~@ scoped_expr)))

  val formals_top = {
    implicit val ctx: Map[Name, Param] = Map()
    P(formals)
  }

  val expr_top = {
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()
    P(expr)
  }

  val formula = expr_top map { case expr =>
    typing.checked(expr, Sort.bool)
  }

  val define_sort: ((Name, List[Param], Option[Type]) => Cmd) = {
    case (name, params, None) =>
      val arity = params.length
      state.con(name, arity)
      DeclareSort(name, arity)

    case (name, params, Some(typ)) =>
      val arity = params.length
      state.con(name, arity)
      state.condef(name, params, typ)
      DefineSort(name, params, typ)
  }

  val define_fun: ((Name, (List[Var], (Type, Option[Expr]))) => Cmd) = {
    case (name, (args, (typ, None))) =>
      state.fun(name, Nil, args.types, typ)
      DeclareFun(name, args.types, typ)

    case (name, (args, (typ, Some(body)))) =>
      val body_ = typing.checked(body, typ)
      state.fun(name, Nil, args.types, typ)
      state.fundef(name, args, body_)
      DefineFun(name, args, typ, body_, true)
  }

  val axiom_ = typing within ("axiom" ~ formula ~ ";")
  val axiom = P(Assert(axiom_))

  val lemma_ = typing within ("lemma" ~ Not(formula) ~ ";")
  val lemma = P(Assert(lemma_))

  def scoped_rhs(bound: List[Var]) = {
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()
    val rhs = P(None(";") | some(braces(scoped_expr(bound))))

    ":" ~ typ ~ rhs
  }

  val const_ =
    typing within ("const" ~ name ~ (ret(Nil: List[Var]) ~@ scoped_rhs))
  val fun_ =
    typing within ("function" ~ name ~ (parens(formals_top) ~@ scoped_rhs))

  val fundef = P(define_fun(const_ | fun_))

  // val sortdef_ = define_sort("type" ~ name ~ gens ~ ("=" ~ typ).? ~ ";")
  // val sortdef = P((context within sortdef_))

  def make_constr
      : ((Name, List[Param], List[Fun], Type) => (Fun, List[Fun])) = {
    case (name, params, sels, res) =>
      (Fun(name, params, sels map (_.res), res), sels)
  }

  def make_datatype: (((Name, List[Param]), List[(Fun, List[Fun])]) => Cmd) = {
    case ((name, params), constrs) =>
      val arity = params.length
      val dt = Datatype(params, constrs)
      DeclareDatatypes(List((name, arity)), List(dt))
  }

  def sel(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(Fun.unary(name ~ ":" ~ ret(params) ~ ret(res) ~ typ))

  def constr(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(make_constr(name ~ ":" ~ ret(params) ~ parens(sel.*) ~ ret(res)))

  def constrs(lhs: (Name, List[Param])) = {
    val ctx: Map[Name, Param] = Map()
    val (name, params) = lhs
    val arity = params.length
    state.con(name, arity)
    val res = state.sort(name, params)
    val inner = constr(params, res, ctx ++ params.asContext)
    inner.*
  }

  val datadecl = P(make_datatype(("data" ~ name ~ gens) ~@ constrs))

  /*
  val arity = P(Arity(sort ~ ret(0)))
  val sel = P(Sel(id ~ ":" ~ typ))
  val sels = parens(sel ~* ",") | ret(Nil)
  val constr = P(Constr(id ~ sels))
  val dt = P(Datatype(ret(Nil) ~ (constr ~* "|")))
  val datadef = P(DeclareDatatype("data" ~ arity ~ "=" ~ dt ~ ";"))


  val cmd = P(sortdef | datadef | axiom | lemma | const | fun)

  val cmds = P(cmd.*)
  val prelude = ret(List[Cmd](SetOption(List(":produce-models", "true"))))
  val postlude = ret(List[Cmd](CheckSat, GetModel))
  val script = P(prelude ++ cmds ++ postlude) */

  /*
  val cmd = P(sortdef | fundef | axiom | lemma)
  val cmds = P(cmd.*)

  val make_script: (List[Cmd] => (List[Cmd], State)) = cmds => (cmds, state)

  val script_ = P(make_script(cmds))
  val script = P(stack within script_) */

  val script: Parser[(List[Cmd], State), Token] = ???

  object syntax extends Syntax[String, Token] {
    val infix_ops = Map(
      ("<==>", (Left, 0)),
      ("==>", (Right, 1)),
      ("||", (Left, 2)),
      ("&&", (Left, 3)),
      ("==", (Left, 5)),
      ("!=", (Left, 5)),
      (">=", (Left, 5)),
      (">", (Left, 5)),
      ("<", (Left, 5)),
      ("<=", (Left, 5)),
      ("+", (Left, 6)),
      ("-", (Left, 6)),
      ("*", (Left, 7)),
      ("/", (Left, 7)),
      ("%", (Left, 7))
    )
    val postfix_ops = Map(
    )
    val prefix_ops = Map(
      ("!", 4),
      ("-", 8)
    )
  }
}

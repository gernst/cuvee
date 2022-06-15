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

object Parser {
  import arse.implicits._

  def parens[A](p: Parser[A, Token]) = "(" ~ p ~ ")"
  def braces[A](p: Parser[A, Token]) = "{" ~ p ~ "}"
  def brackets[A](p: Parser[A, Token]) = "[" ~ p ~ "]"
  def angle[A](p: Parser[A, Token]) = "<" ~ p ~ ">"

  def none[A](p: Parser[A, Token]) = p map { a => None }
  def some[A](p: Parser[A, Token]) = p map { a => Some(a) }

  object stack extends DynamicVariable(State.default) {
    def within[A](p: Parser[A, Token]) =
      S(p, this)
  }

  def state = stack.value

  object context extends Scope[Name, Param] {}

  object scope extends Scope[Name, Var] {
    val declare: ((Name, Type) => Var) = { case (name, typ) =>
      val x = Var(name, typ)
      scope update (name, x)
      x
    }
  }

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
  val opname = V[String]
  val number = V[String]
  val string = V[String]
  val quant = V[String]

  val name = P(Name(id))

  val con = P(state.cons(name))
  val gen = P(Param.from(name))
  val gens = P(angle(gen ~* ",") | ret(Nil))

  def make_sort: ((Name, List[Type]) => Type) = {
    case (name, Nil) if context contains name =>
      context(name)
    case (name, args) if state.cons contains name =>
      Sort(state.cons(name), args)
  }

  val typ: Parser[Type, Token] = P(array | int | bool | real | sort)
  val int = P(Sort.int("int"))
  val bool = P(Sort.bool("bool"))
  val real = P(Sort.real("real"))

  val inst = P(angle(typ ~* ",") | ret(Nil))
  val sort = P(make_sort(name ~ inst))
  val array = P(Sort.array(brackets(typ) ~ typ))

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

  def make_app: ((Name, List[Expr]) => Expr) = {
    case (name, Nil) if scope contains name =>
      scope(name)
    case (name, args) if state.funs contains (name, args.length) =>
      typing.app(name, args)
    case (name, Nil) =>
      error("unknown variable or constant: " + name)
    case (name, _) =>
      error("unknown function: " + name)
  }

  def make_bind: ((String, List[Var], Expr) => Expr) = {
    case (name, bound, body) =>
      typing.bind(name, bound, body, Sort.bool)
  }

  val op = P(opname)
  val args = P(parens(expr ~* ",") | ret(Nil))
  val app = P(make_app(name ~ args))

  val expr: Parser[Expr, Token] = M(inner, op, make_op, syntax)
  val inner: Parser[Expr, Token] = P(
    parens(expr) | num | ite | bind | map | app
  )

  def make_int: (String => Expr) = { case text =>
    Lit(BigInt(text), Sort.int)
  }

  val num = P(make_int(number))
  val update = P(":=" ~ expr)
  val access = P(brackets(expr ~ update.?))

  val zip: ((Expr, List[(Expr, Option[Expr])]) => Expr) = {
    case (base, Nil) =>
      base
    case (base, (index, None) :: rest) =>
      zip(Select(base, index), rest)
    case (base, (index, Some(value)) :: rest) =>
      zip(Store(base, index, value), rest)
  }

  val map = P(zip(app ~ access.*))
  val ite = P(Ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

  val formal = P(scope.declare(name ~ ":" ~ typ))
  val formals = P(formal ~* ",")
  val bind = P(make_bind(scope within (quant ~ formals ~ "::" ~ expr)))

  val assert: (Expr => Cmd) = { case expr =>
    val expr_ = typing.checked(expr, Sort.bool)
    Assert(expr_)
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

  val define_fun: ((Name, List[Var], Type, Option[Expr]) => Cmd) = {
    case (name, args, typ, None) =>
      state.fun(name, Nil, args.types, typ)
      DeclareFun(name, args.types, typ)

    case (name, args, typ, Some(body)) =>
      val body_ = typing.checked(body, typ)
      state.fun(name, Nil, args.types, typ)
      state.fundef(name, args, body_)
      DefineFun(name, args, typ, body_, true)
  }

  val axiom_ = typing within assert("axiom" ~ expr ~ ";")
  val axiom = P(axiom_)

  val lemma_ = typing within assert("lemma" ~ Not(expr) ~ ";")
  val lemma = P(lemma_)

  val funsig =
    ("function" ~ name ~ parens(formals)) | ("const" ~ name ~ ret[List[
      Var
    ], Token](Nil))

  val body = P(None(";") | some(braces(expr)))
  val fundef__ = define_fun(
    funsig ~ ":" ~ typ ~ body
  )
  val fundef_ = typing within fundef__
  val fundef = P(scope within fundef_)

  val sortdef_ = define_sort("type" ~ name ~ gens ~ ("=" ~ typ).? ~ ";")
  val sortdef = P((context within sortdef_))

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

  val cmd = P(sortdef | fundef | axiom | lemma)
  val cmds = P(cmd.*)

  val make_script: (List[Cmd] => (List[Cmd], State)) = cmds => (cmds, state)

  val script_ = P(make_script(cmds))
  val script = P(stack within script_)

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

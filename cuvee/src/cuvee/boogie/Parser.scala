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

  object stack extends DynamicVariable(State.default) {}
  def state = stack.value

  object context extends Scope[String, Param] {}

  object scope extends Scope[String, Var] {
    val declare: ((String, Type) => Var) = { case (name, typ) =>
      val x = Var(name, typ)
      scope update (name, x)
      x
    }
  }

  object typing extends Scope[Param, Type] {
    def unify(typ1: Type, typ2: Type) {
      value = Type.unify(typ1, typ2, value)
    }

    def unify(types1: List[Type], types2: List[Type]) {
      value = Type.unify(types1, types2, value)
    }

    def app(name: String, args: List[Expr]) = {
      val fun = state funs name
      val inst = fun.generic
      unify(inst.args, args.types)
      App(inst, args)
    }

    def bind(
        name: String,
        bound: List[Var],
        body: Expr,
        typ: Type
    ) = {
      val quant = Quant(name)
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
  val name = V[String]
  val opname = V[String]
  val number = V[String]
  val string = V[String]
  val quant = V[String]

  val con = P(state.cons(name))
  val gen = P(Param.from(name))
  val gens = P(angle(gen ~* ",") | ret(Nil))

  def make_sort: ((String, List[Type]) => Type) = {
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

  def translate: (String => String) = {
    case "<==>" => "="
    case "==>"  => "=>"
    case "&&"   => "and"
    case "||"   => "or"
    case "=="   => "="
    case "!="   => "distinct"
    case "/"    => "div"
    case "%"    => "mod"
    case "!"    => "not"
    case op     => op
  }

  def make_app: ((String, List[Expr]) => Expr) = {
    case (name, Nil) if scope contains name =>
      scope(name)
    case (name, args) if state.funs contains name =>
      typing.app(name, args)
  }

  def make_bind: ((String, List[Var], Expr) => Expr) = {
    case (name, bound, body) =>
      typing.bind(name, bound, body, Sort.bool)
  }

  val op = P(translate(opname))
  val args = P(parens(expr ~* ",") | ret(Nil))
  val app = P(make_app(name ~ args))

  val expr: Parser[Expr, Token] = M(inner, op, make_app, Syntax)
  val inner: Parser[Expr, Token] = P(
    parens(expr) | num | ite | bind | map
  )

  def make_int: (String => Expr) = {
    case text =>
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
  val bind = P(make_bind(scope within (quant ~ formals ~ "." ~ expr)))

  val assert: (Expr => Cmd) = { case expr =>
    val expr_ = typing.checked(expr, Sort.bool)
    Assert(expr_)
  }

  val define_sort: ((String, List[Param], Option[Type]) => Cmd) = {
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

  val define_fun: ((String, List[Var], Type, Option[Expr]) => Cmd) = {
    case (id, args, typ, None) =>
      DeclareFun(id, args.types, typ)

    case (id, args, typ, Some(body)) =>
      val body_ = typing.checked(body, typ)
      DefineFun(id, args, typ, body_, true)
  }

  val axiom_ = typing within assert("axiom" ~ expr ~ ";")
  val axiom = P(axiom_)

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

  val cmd = P(sortdef | fundef | axiom)
  val cmds = P(cmd.*)
}

object Syntax extends Syntax[String, Token] {
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

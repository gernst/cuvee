package cuvee.boogie

import arse._

import cuvee._
import cuvee.State
import cuvee.backend._
import cuvee.pure._
import cuvee.imp._
import cuvee.util.Name
import cuvee.smtlib.Cmd
import cuvee.smtlib.Assert
import cuvee.smtlib.DeclareFun
import cuvee.smtlib.DefineFun
import cuvee.smtlib.DeclareSort
import cuvee.smtlib.DefineSort
import cuvee.smtlib.Lemma
import scala.util.DynamicVariable
import cuvee.smtlib.DeclareDatatypes
import cuvee.smtlib.DeclareProc
import cuvee.smtlib.DefineProc

object Parser {
  import arse.implicits._

  // shadow existing definition for T = Token
  def ret[A](a: A) =
    new arse.Parser.Accept[A, Token](a)

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

  val a = Param("a")
  state.fun("old", List(a), List(a), a)

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
      unify(body.typ, typ)
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

  val la = just(op filter (_ == "<"))
  val ra = just(op filter (_ == ">"))

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
    // "!=" -> "distinct",
    "/" -> "div",
    "%" -> "mod",
    "!" -> "not"
  )

  def make_op: ((String, List[Expr]) => Expr) = {
    case ("!=", List(arg1, arg2)) =>
      Not(Eq(arg1, arg2))

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

  def make_var(scope: Map[Name, Var]): (Name => Var) = {
    case name if scope contains name =>
      scope(name)
    case name =>
      error(s"unknown variable: ${name.toString}")
  }

  def var_(implicit scope: Map[Name, Var]) =
    P(make_var(scope)(name))

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
      DefineFun(name, args, typ, body_, body.funs exists (_.name == name))
  }

  val define_proc: ((Name, ((List[Var], List[Var]), Option[Prog])) => Cmd) = {
    case (name, ((in, out), None)) =>
      state.proc(name, Nil, in.types, out.types)
      DeclareProc(name, in.types, out.types)

    case (name, ((in, out), Some(body))) =>
      state.proc(name, Nil, in.types, out.types)
      state.procdef(name, in, out, body)
      DefineProc(name, in, out, body)
  }

  val axiom_ = typing within ("axiom" ~ formula ~ ";")
  val axiom = P(Assert(axiom_))

  /* TACTICS */
  // SORRY
  val sorry = P(Sorry(KW("sorry")));

  // INDUCTION
  def make_pat(typ: Type): (Name => Parser[Expr, Token]) = {
    // Check if name identifies a constructor of the correct type
    case name if state.constrs exists (_.name == name) =>
      val sort = typ.asInstanceOf[Sort]
      val dt = state.datatypes(sort.con.name)

      dt.constrs.find(_._1.name == name) match {
        case None => error("Could not find constructor")
        case Some((con, _)) =>
          val su = Type.bind(con.res, typ)
          val inst = Inst(con, su)

          val mkapp: (List[Expr] => Expr) = l => App(inst, l)

          P(mkapp(patargs(inst)))
      }
    // Otherwise, it's a variable
    case name =>
      P(ret(Var(name, typ)))
  }

  def pat(implicit typ: Type): Parser[Expr, Token] =
    P(name ~>@ make_pat(typ))

  def patargs(inst: Inst): Parser[List[Expr], Token] = {
    val ts = inst.args
    if (ts.isEmpty)
      ret(Nil)
    else {
      val ps = ts map (t => pat(t))
      parens(ps.join(","))
    }
  }

  def case_(
      scope: Map[Name, Var]
  )(implicit typ: Type, ctx: Map[Name, Param]): Parser[(Expr, Tactic), Token] =
    pat(typ) ~ "->" ~@ (e => {
      val xs = e.free
      val scope_ = scope ++ xs.map { x => (x.name, x) }
      tactic(scope_, ctx)
    })

  def induction(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Induction, Token] =
    P(
      "induction" ~ Induction(
        var_ ~@ (v => case_(scope)(v.typ, ctx) ~* ",")
      ) ~ "end"
    );

  // SHOW
  def show(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      "show" ~ Show(
        (typing within formula) ~@ (phi =>
          ("proof" ~ scoped_tactic(phi)).?
        ) ~ ("then" ~ tactic).?
      ) ~ "end"
    )

  // ANY TACTIC
  def tactic(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Tactic, Token] =
    P(sorry | show | induction);

  def scoped_tactic(
      phi: Expr
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    def collect_all_the_vars(phi: Expr): List[Var] = phi match {
      case Forall(bound, body) =>
        bound ++ collect_all_the_vars(body)
      case _ =>
        Nil
    }

    val xs = collect_all_the_vars(phi)
    tactic(scope ++ xs.asScope, ctx)
  }

  def lemma_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    ("lemma" ~ (typing within formula) ~@ (phi =>
      ("proof" ~ scoped_tactic(phi)).?
    ) ~ ";")
  def lemma(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(
    Lemma(lemma_)
  )

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

  def prog(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    P(spec | ctrl | if_ | while_ | assign)

  val ctrl = Break("break" ~ ";") | Return("return" ~ ";") 

  def if_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(If("if" ~ parens(expr) ~ block ~ ("else" ~ block).?))

  def aux(what: String)(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    what ~ expr ~ ";"

  def while_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      While(
        "while" ~ parens(expr) ~ aux("decreases").? ~ aux("invariant").? ~ aux(
          "summary"
        ).? ~ ret(Nil) ~ block
      )
    )

  def spec(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      Spec.assume("assume" ~ expr ~ ";") | Spec.assert(
        "assert" ~ expr ~ ";"
      ) | Spec.havoc("havoc" ~ (var_ ~+ ",") ~ ";")
    )

  def assign(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    Assign((var_ ~+ ",") ~ ":=" ~ (expr ~+ ",") ~ ";")

  def local(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    Local("var" ~ (formal ~+ ",") ~ (":=" ~ (expr ~+ ",")).? ~ ";")

  def block_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[List[Prog], Token] =
    P(
      ("}" ~ ret(Nil)) | (local ::@ (prog =>
        block_(scope ++ prog.xs.asScope, ctx)
      )) | (prog :: block_)
    )

  def block(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    Block("{" ~ block_)

  def scoped_block(
      bound: List[Var]
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    block(scope ++ bound.asScope, ctx)
  }

  val scoped_body = (sig: (List[Var], List[Var])) => {
    val (in, out) = sig
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()

    P(None(";") | some(scoped_block(in ++ out)))
  }

  val maybe_returns = ("returns" ~ parens(formals_top)) | ret(Nil)
  val proc_ =
    "procedure" ~ name ~ (parens(formals_top) ~ maybe_returns ~@ scoped_body)

  val proc = P(define_proc(proc_))

  def sortdef_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    define_sort("type" ~ name ~ gens ~ ("=" ~ typ).? ~ ";")
  def sortdef(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(
    (typing within sortdef_)
  )

  def make_constr
      : ((Name, List[Param], List[Fun], Type) => (Fun, List[Fun])) = {
    case (name, params, sels, res) =>
      // declare the constructor
      state.fun(name, params, sels map (_.res), res)
      // declare projections for the selectors
      for (sel <- sels) {
        state.fun(sel.name, sel.params, sel.args, sel.res)
      }

      (Fun(name, params, sels map (_.res), res), sels)
  }

  def make_datatype: (((Name, List[Param]), List[(Fun, List[Fun])]) => Cmd) = {
    case ((name, params), constrs) =>
      val arity = params.length
      val dt = Datatype(params, constrs)
      state.datatype(name, dt)
      DeclareDatatypes(List((name, arity)), List(dt))
  }

  def sel(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(Fun.unary(name ~ ret(params) ~ ":" ~ ret(res) ~ typ))

  def sels(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    parens(sel ~* ",") | ret(Nil)

  def constr(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(make_constr(name ~ ret(params) ~ sels ~ ret(res)))

  def constrs(lhs: (Name, List[Param])) = {
    val ctx: Map[Name, Param] = Map()
    val (name, params) = lhs
    val arity = params.length
    state.con(name, arity)
    val res = state.sort(name, params)
    val inner = constr(params, res, ctx ++ params.asContext)
    inner ~* "|"
  }

  val datadef = P(make_datatype(("data" ~ name ~ gens ~ "=") ~@ constrs ~ ";"))

  def cmd(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(
    sortdef | datadef | fundef | axiom | lemma | proc
  )
  def cmds(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(cmd.*)

  val make_script: (List[Cmd] => (List[Cmd], State)) = cmds => (cmds, state)

  def script_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(
    make_script(cmds)
  )
  def script(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = P(
    stack within script_
  )

  // val script: Parser[(List[Cmd], State), Token] = ???

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

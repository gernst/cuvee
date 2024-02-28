package cuvee.boogie

import easyparse._
import easyparse.implicits._

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._
import cuvee.prove._
import cuvee.smtlib.Assert
import cuvee.smtlib.Lemma

class Grammar(parser: cuvee.boogie.Parser) {
  import easyparse.implicits._

  import parser._
  import cuvee.boogie.Parser._

  // shadow existing definition for T = Token
  def ret[A](a: A) =
    new easyparse.Parser.Accept[A, Token](a)

  def parens[A](p: Parser[A, Token]) = "(" ~ p ~ ")"
  def braces[A](p: Parser[A, Token]) = "{" ~ p ~ "}"
  def brackets[A](p: Parser[A, Token]) = "[" ~ p ~ "]"
  def angle[A](p: Parser[A, Token]) = la ~ p ~ ra

  def none[A](p: Parser[A, Token]) = p map { a => None }
  def some[A](p: Parser[A, Token]) = p map { a => Some(a) }

  def make_int: (String => BigInt) = text => BigInt(text)
  def make_int_lit: (String => Expr) = text => Lit(make_int(text), Sort.int)

  val num = P(make_int_lit(number))
  val int_ = P(make_int(number))

  val name = P(Name(id))

  val la = just(op filter (_ == "<"))
  val ra = just(op filter (_ == ">"))

  val con = P(state.cons(name))
  val gen = P(Param.from(name))
  val gens = P(angle(gen ~* ",") | ret(Nil))

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

  def var_(implicit scope: Map[Name, Var]) =
    P(make_var(scope)(name))

  def formal(implicit ctx: Map[Name, Param]) =
    P(Var(name ~ ":" ~ typ))

  def formals(implicit ctx: Map[Name, Param]) =
    P(formal ~* ",")

  object unresolved {
    def expr(implicit
        scope: Map[Name, Var],
        ctx: Map[Name, Param]
    ): Parser[Expr, Token] =
      M(inner, op, make_op, Grammar.syntax)

    def inner(implicit
        scope: Map[Name, Var],
        ctx: Map[Name, Param]
    ): Parser[Expr, Token] =
      P(parens(expr) | num | ite | bind | map)

    def args(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(parens(expr ~+ ",") | ret(Nil))

    def app(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_app(scope)(name ~ args))

    def update(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(":=" ~ expr)
    def access(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(brackets(expr ~ update.?))

    val zip: ((Expr, List[(Expr, Option[Expr])]) => Expr) = {
      case (base, Nil) =>
        base
      case (base, (index, None) :: rest) =>
        zip(make_select(base, index), rest)
      case (base, (index, Some(value)) :: rest) =>
        zip(make_store(base, index, value), rest)
    }

    def map(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(zip(app ~ access.*))
    def ite(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

    def scoped_expr(
        bound: List[Var]
    )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      expr(scope ++ bound.asScope, ctx)

    def bind(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_bind(quant ~ (formals ~ "::" ~@ scoped_expr)))
  }

  def expr(typ: Type)(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Expr, Token] = {
    typing within make_typed_expr(typ)(unresolved.expr)
  }

  def expr(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Expr, Token] = {
    typing within make_expr(unresolved.expr)
  }

  def formula(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Expr, Token] = {
    typing within make_formula(unresolved.expr)
  }

  def prog(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    P(spec | ctrl | if_ | while_ | assign)

  val ctrl =
    Break("break" ~ ";") | Return("return" ~ ";")

  def else_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    block | if_

  def if_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    P(If("if" ~ parens(formula) ~ block ~ ("else" ~ else_).?))

  def havoc(kw: String)(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.havoc(kw ~ (var_ ~+ ",") ~ ";"))

  def assume(
      kw: String
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.assume(kw ~ formula ~ ";"))

  def assume_final_to_old(
      kw: String
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.assume(kw ~ final_to_old(formula) ~ ";"))

  def assert(
      kw: String
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.assert(kw ~ formula ~ ";"))

  def decreases(
      kw: String
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(kw ~ expr(Sort.int) ~ ";")

  def spec(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(assert("assert") | assume("assume") | havoc("havoc"))

  def loop_spec(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(assert("invariant") | assume_final_to_old("summary"))

  def proc_spec(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(assert("requires") | assume("ensures") | havoc("modifies"))

  def while_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    val head =
      "while" ~ parens(formula) ~ decreases("decreases").? ~ merge(loop_spec.*)
    P(While(head ~ block))
  }

  def assign(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Assign((var_ ~+ ",") ~ ":=" ~ (expr ~+ ",") ~ ";"))
  // TODO: we can narrow the type of expr to that of the corresponding var

  def local(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Local("var" ~ (formal ~+ ",") ~ (":=" ~ (expr ~+ ",")).? ~ ";"))
  // TODO: we can narrow the type of expr to that of the corresponding var

  val block_end =
    "}" ~ ret(Nil)

  def block_local(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    (local ::@ (prog => block_(scope ++ prog.xs.asScope, ctx)))

  def block_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[List[Prog], Token] =
    P(block_end | block_local | (prog :: block_))

  def block(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Block("{" ~ block_))

  def scoped_body(implicit ctx: Map[Name, Param]) =
    (sig: (List[Var], List[Var])) => {
      // import toplevel.scope

      val (in, out) = sig
      val bound = in ++ out
      implicit val scope = toplevel.scope ++ bound.asScope

      val body = None(";") | some(block)

      maybe_merge(proc_spec.*) ~ body
    }

  def maybe_returns(implicit ctx: Map[Name, Param]) =
    ("returns" ~ parens(formals)) | ret(Nil)

  def proc(implicit ctx: Map[Name, Param]) = {
    P(((parens(formals) ~ maybe_returns) ~@ scoped_body))
  }

  def rhs(name: Name, params: List[Param])(implicit ctx: Map[Name, Param]) =
    (sig: (List[Var] ~ Type)) => {
      // register the function name here to allow for recursive definitions
      val (bound ~ res) = sig
      state.fun(name, params, bound.types, res)

      val scope: Map[Name, Var] = Map()
      None(";") | some(braces(expr(res)(scope ++ bound.asScope, ctx)))
    }

  def gen_rhs(xs: Map[Name, Param] => Parser[List[Var], Token]) =
    (from: (Name ~ List[Param])) => {
      val (name ~ params) = from
      implicit val ctx = Map(params.asContext: _*)
      xs(ctx) ~ ":" ~ typ ~@ rhs(name, params)
    }

  val axiom = {
    import toplevel.scope
    import toplevel.ctx
    P(Assert("axiom" ~ formula ~ ";"))
  }

  val constdef =
    P(define_fun("const" ~ name ~ gens ~@ gen_rhs(ctx => ret(Nil))))

  val fundef =
    P(define_fun("function" ~ name ~ gens ~@ gen_rhs(ctx => parens(formals(ctx)))))

  // val constdef = {
  //   import toplevel.ctx
  //   P(define_fun("const" ~ name ~ ret(Nil: List[Var]) ~ ":" ~ typ ~@ rhs))
  // }

  // val fundef = {
  //   import toplevel.ctx
  //   P(define_fun("function" ~ name ~ parens(formals) ~ ":" ~ typ ~@ rhs))
  // }

  def gen_proc[A] =
    (from: (Name ~ List[Param])) => {
      val (name ~ params) = from
      implicit val ctx = Map(params.asContext: _*)
      proc(ctx)
    }

  val procdef =
    P(define_proc("procedure" ~ name ~ gens ~@ gen_proc))

  def sortdef(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(define_sort("type" ~ name ~ gens ~ ("=" ~ typ).? ~ ";"))

  def sel(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(Fun.unary(name ~ ret(params) ~ ":" ~ ret(res) ~ typ))

  def sels(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    parens(sel ~* ",") | ret(Nil)

  def constr(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(make_constr(name ~ ret(params) ~ sels ~ ret(res)))

  def constrs(lhs: (Name, List[Param])) = {
    val ctx: Map[Name, Param] = Map()
    val (dt, params) = lhs
    val arity = params.length
    state.con(dt, arity)
    val res = state.sort(dt, params)
    val inner = constr(params, res, ctx ++ params.asContext)
    inner ~* "|"
  }

  /* TACTICS */
  // SORRY
  val sorry =
    P(Sorry(KW("sorry")));

  // INDUCTION
  def patargs(typ: Type): (Name => Parser[Expr, Token]) = {
    // Check if name identifies a constructor of the correct type
    case name if state.constrs exists (_.name == name) =>
      val sort = typ.asInstanceOf[Sort]
      val dt = state.datatypes(sort.con.name)

      dt.constrs.find(_._1.name == name) match {
        case None => cuvee.error("Could not find constructor")
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

  def patargs(inst: Inst): Parser[List[Expr], Token] = {
    val ts = inst.args
    if (ts.isEmpty)
      ret(Nil)
    else {
      val ps = ts map (t => pat(t))
      parens(ps.join(","))
    }
  }

  def pat(implicit typ: Type): Parser[Expr, Token] =
    P(name ~>@ patargs(typ))

  def case_(typ: Type)(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("case" ~ pat(typ) ~ "=>" ~@ (expr => tactic(scope ++ expr.free.asScope, ctx)))

  def cases(arg: Expr)(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    braces(case_(arg.typ).*) | ret(Nil)

  def induction(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Induction("induction" ~ var_ ~@ cases));

  def maybe_proof(
      phi: Expr
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("proof" ~ scoped_tactic(phi)).?

  // SHOW
  def show(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Show("show" ~ formula ~@ maybe_proof ~ ("then" ~ tactic).?))

  // UNFOLD
  def unfold(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      Unfold(
        "unfold" ~ make_fun_ref(
          name ~ ("[" ~ int_ ~ "]").?
        ) ~ ("at" ~ (int_ ~+ ",")).? ~ ("then" ~ tactic).?
      )
    )

  // AUTO
  def auto(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = "auto" ~ ret(Auto)

  // NOAUTO
  def noauto(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(NoAuto("noauto" ~ tactic))

  // ANY TACTIC
  def tactic(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Tactic, Token] =
    P(sorry | show | induction | unfold | auto | noauto);

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

  def lemma(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Lemma("lemma" ~ formula ~@ maybe_proof ~ ";" ~ ret(true)))

  val datadef =
    P(make_datatype(("data" ~ name ~ gens ~ "=") ~@ constrs ~ ";"))

  def cmd(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(sortdef | datadef | constdef | fundef | procdef | axiom | lemma | easyparse.Parser.Fail())

  def cmds(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(cmd.*)

  def script(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_script(cmds))
}

object Grammar {
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

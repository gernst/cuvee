package cuvee.boogie

import arse._
import arse.implicits._

import cuvee.util.Name
import cuvee.pure._
import cuvee.imp._

object Grammar {
  import cuvee.boogie.Parser._

  def prog(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    P(spec | ctrl | if_ | while_ | assign)

  val ctrl = Break("break" ~ ";") | Return("return" ~ ";")

  def else_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    block | if_

  def if_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Prog, Token] =
    P(If("if" ~ parens(expr) ~ block ~ ("else" ~ else_).?))

  def aux(what: String)(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    what ~ expr ~ ";"

  def while_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      While(
        "while" ~ parens(expr) ~ aux("decreases").? ~ aux("invariant").* ~ aux(
          "summary"
        ).* ~ ret(Nil) ~ block
      )
    )

  def assume(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.assume("assume" ~ expr ~ ";"))

  def assert(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Spec.assert("assert" ~ expr ~ ";"))

  def havoc(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    Spec.havoc("havoc" ~ (var_ ~+ ",") ~ ";")

  def spec(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(assume | assert | havoc)

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
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    block(scope ++ bound.asScope, ctx)

  def scoped_rhs(bound: List[Var]) = {
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()
    val rhs = None(";") | some(braces(scoped_expr(bound)))

    ":" ~ typ ~ rhs
  }

  val scoped_body = (sig: (List[Var], List[Var])) => {
    val (in, out) = sig
    implicit val scope: Map[Name, Var] = Map()
    implicit val ctx: Map[Name, Param] = Map()

    None(";") | some(scoped_block(in ++ out))
  }

  val maybe_returns =
    ("returns" ~ parens(formals_top)) | ret(Nil)

  val proc =
    P((parens(formals_top) ~ maybe_returns ~@ scoped_body))

  val const_ =
    typing within ("const" ~ name ~ (ret(Nil: List[Var]) ~@ scoped_rhs))

  val fun_ =
    typing within ("function" ~ name ~ (parens(formals_top) ~@ scoped_rhs))

  val fundef = P(define_fun(const_ | fun_))

  val procdef =
    P(define_proc("procedure" ~ name ~ proc))

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

  val datadef =
    P(make_datatype(("data" ~ name ~ gens ~ "=") ~@ constrs ~ ";"))

  def cmd(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(sortdef | datadef | fundef | procdef | axiom | lemma)

  def cmds(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(cmd.*)

  def script_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_script(cmds))

  def script(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(stack within script_)
}

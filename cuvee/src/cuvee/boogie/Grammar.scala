package cuvee.boogie

import easyparse._
import easyparse.implicits._

import cuvee.util.Name
import cuvee.sexpr
import cuvee.pure._
import cuvee.imp._
import cuvee.prove._
import cuvee.smtlib.Assert
import cuvee.smtlib.Lemma
import cuvee.smtlib.Cmd
import cuvee.smtlib.Free
import cuvee.smtlib.Goal
import cuvee.imp.Mode.In
import cuvee.imp.Mode.Out
import cuvee.imp.Mode.InOut
import cuvee.imp.traces._

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
  def bags[A](p: Parser[A, Token]) = "⟅" ~ p ~ "⟆"
  def sqbraces[A](p: Parser[A, Token]) = "⦃" ~ p ~ "⦄"
  def sembrackets[A](p: Parser[A, Token]) = "〚" ~ p ~ "〛"

  // angular brackets are also operators, hence cannot match literal strings
  def angle[A](p: Parser[A, Token]) = la ~ p ~ ra
  def sangle[A](p: Parser[A, Token]) = "〈" ~ p ~ "〉"
  def dangle[A](p: Parser[A, Token]) = "⟪" ~ p ~ "⟫"

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

  def var_generic =
    P(Var(name ~ ret(Param.fresh("a"))))

  def var_(implicit scope: Map[Name, Var]) =
    P(make_var(scope)(name))

  def formal(implicit ctx: Map[Name, Param]) =
    P(Var(name ~ ":" ~ typ))

  // def formals(implicit ctx: Map[Name, Param]) =
  //   P(formal ~* ",")

  def mode: Parser[Mode, Token] =
    P(In("in") | Out("out") | InOut("inout"))

  def formalWithMode(implicit ctx: Map[Name, Param]) =
    P(name ~ ":" ~ mode ~ typ map { case (n ~ m ~ t) => (m, Var(n, t)) })

  // def formalsWithMode(implicit ctx: Map[Name, Param]) =
  //   P(formalWithMode ~* ",")

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
      P(parens(expr) | num | wp | box | dia | ite | bind | trace | mapping | invariant | map)

    def args(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(parens(expr ~+ ",") | ret(Nil))

    def map(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(zip((at | app) ~ apply.? ~ access.*))

    def app(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_app(scope)(name ~ args))

    def access(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(brackets(expr ~ (":=" ~ expr).?))

    def apply(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(sembrackets(expr))

    val zip: ((Expr, Option[Expr], List[(Expr, Option[Expr])]) => Expr) = {
      case (base, Some(arg), Nil) =>
        make_select_(base, arg)
      case (base, None, Nil) =>
        base
      case (base, None, (index, None) :: rest) =>
        zip(make_select(base, index), None, rest)
      case (base, None, (index, Some(value)) :: rest) =>
        zip(make_store(base, index, value), None, rest)
    }

    def ite(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_ite("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

    // warning: not type-checked here!
    def iteration[A](implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
      P(make_iteration("for" ~ (var_generic ~* ",") ~ "<-" ~ (expr ~* ",")))
    }

    // def counter(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    //   P(
    //     Counter(
    //       "counter" ~ "(" ~ var_ ~ "," ~ iteration ~ "while" ~ formula ~ "unless" ~ formula ~ ")"
    //     )
    //   )

    // warning: not type-checked here!
    def update(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(Update("if" ~ expr ~ "then" ~ expr)) | P(Update(ret(True) ~ expr))

    def scoped_result(
        formals: List[LetEq]
    )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
      val bound = formals.vars
      val scope_ = scope ++ bound.asScope
      "yield" ~ expr(scope_, ctx)
    }

    def scoped_updates(
        formals: List[LetEq]
    )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
      "do" ~ var_generic ~ ":=" ~@ { x =>
        val bound = x :: formals.vars
        val scope_ = scope ++ bound.asScope
        (update(scope_, ctx) ~* "|")
      }
    }

    def mapping(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_mapping("map" ~ "(" ~ (iteration ~@ scoped_result) ~ ")"))

    def invariant(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_invariant("invariant" ~ "(" ~ (iteration ~@ scoped_result) ~ ")"))

    def trace(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_trace("trace" ~ "(" ~ expr ~ "," ~ (iteration ~@ scoped_updates) ~ ")"))

    def wp(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(WP(dangle(block_) ~ formula))

    def box(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(Box(brackets(block_) ~ formula))

    def dia(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(Dia(angle(block_) ~ formula))

    def scoped_expr(
        bound: List[Var]
    )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
      val scope_ = scope ++ bound.asScope
      val expr_ = expr(scope_, ctx)

      val trigger = braces(expr_ ~+ ",") | ret(Nil)
      trigger ~ expr_
    }

    def bind(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_bind(quant ~ ((formal ~+ ",") ~ "::" ~@ scoped_expr)))

    def at(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
      P(make_at(loc ~ "(" ~ expr ~ ")"))
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
    P(spec | ctrl | if_ | while_ | call | block | assign)

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
    P(assert("requires") | assume("ensures"))

  def while_(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    val head =
      "while" ~ parens(formula) ~ decreases("decreases").? ~ merge(loop_spec.*)
    P(While(head ~ block))
  }

  // def assign(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
  //   P(Assign(vars1 ~ ":=" ~ (expr ~+ ",") ~ ";"))
  // TODO: we can narrow the type of expr to that of the corresponding var

  def assign(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Assign.froms((expr ~+ ",") ~ ":=" ~ (expr ~+ ",") ~ ";"))

  def call(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_call((var_ ~+ ",") ?~ ":=" ?~ "call" ~ name ~ parens(expr ~* ",") ~ ";"))

  def local(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Local("var" ~ (formal ~+ ",") ~ (":=" ~ (expr ~+ ",")).? ~ ";"))
  // TODO: we can narrow the type of expr to that of the corresponding var

  def block_local(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    (local ::@ { case Local(xs, init) => block_(scope ++ xs.asScope, ctx) })

  def block_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[List[Prog], Token] =
    P(block_local | (prog :: block_) | ret(Nil))

  def block(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Block(braces(block_)))

  def scoped_body(implicit ctx: Map[Name, Param]) =
    (sig: (List[Var] ~ List[Var] ~ List[Var])) => {
      // import toplevel.scope

      val (in ~ out ~ mod) = sig
      val bound = in ++ out ++ mod
      implicit val scope = toplevel.scope ++ bound.asScope

      val body = None(";") | some(block)

      maybe_merge(mod)(proc_spec.*) ~ body
    }

  def scoped_behaviors(implicit ctx: Map[Name, Param]) =
    (sig: List[(Mode, Var)]) => {
      val (modes, bound) = sig.unzip
      implicit val scope = toplevel.scope ++ bound.asScope

      val pre = P("requires" ~ formula ~ ";")
      val post = P("ensures" ~ formula ~ ";")

      val pair = P(And(pre.*) ~ And(post.+))

      pair ~* "also"
    }

  def maybe_returns(implicit ctx: Map[Name, Param]) =
    ("returns" ~ parens(formal ~+ ",")) | ret(Nil)

  def maybe_modifies(implicit scope: Map[Name, Var]) =
    ("modifies" ~ (var_ ~* ",") ~ ";") | ret(Nil)

  def proc(implicit ctx: Map[Name, Param]) = {
    implicit val scope = state.vars
    P(((parens(formal ~* ",") ~ maybe_returns ~ maybe_modifies) ~@ scoped_body))
  }

  def contract(implicit ctx: Map[Name, Param]) = {
    implicit val scope = state.vars
    P((parens(formalWithMode ~* ",") ~@ scoped_behaviors))
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
    P(define_fun("function" ~ name ~ gens ~@ gen_rhs(ctx => parens((formal(ctx) ~* ",")))))

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

  def gen_contract[A] =
    (from: (Name ~ List[Param])) => {
      val (name ~ params) = from
      implicit val ctx = Map(params.asContext: _*)
      contract(ctx)
    }

  val vardecl = {
    import toplevel.ctx
    P(declare_var("var" ~ name ~ ":" ~ typ ~ ";"))
  }

  val procdef =
    P(define_proc("procedure" ~ name ~ gens ~@ gen_proc))

  val contractdef =
    P(define_contract("contract" ~ name ~ gens ~@ gen_contract))

  def sortdef(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(define_sort("type" ~ name ~ gens ~ ("=" ~ typ).? ~ ";"))

  def sel(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(Fun.unary(name ~ ret(params) ~ ":" ~ ret(res) ~ typ))

  def sels(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    parens(sel ~* ",") | ret(Nil)

  def constr(implicit params: List[Param], res: Type, ctx: Map[Name, Param]) =
    P(make_constr(name ~ ret(params) ~ sels ~ ret(res)))

  def constrs(declare: Boolean)(lhs: (Name, List[Param])) = {
    val ctx: Map[Name, Param] = Map()
    val (dt, params) = lhs
    if (declare) {
      val arity = params.length
      state.con(dt, arity)
    }

    val res = state.sort(dt, params)
    val inner = constr(params, res, ctx ++ params.asContext)
    inner ~* "|"
  }

  /* TACTICS */
  // SORRY
  val sorry =
    P(Proof(Sorry(KW("sorry")) ~ ret(Nil)));

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

  def constargs(typ: Type): ((Name) => Parser[(Fun, Expr), Token]) = {
    case name if state.constrs exists (_.name == name) =>
      val sort = typ.asInstanceOf[Sort]
      val dt = state.datatypes(sort.con.name)

      dt.constrs.find(_._1.name == name) match {
        case None => cuvee.error("Could not find constructor")
        case Some((con, sels)) =>
          val su = Type.bind(con.res, typ)
          val inst = Inst(con, su)

          val mkapp: (List[Expr] => Expr) = l => App(inst, l)

          P(ret(con) ~ mkapp(patargs(inst)))
      }

    case _ => cuvee.error("Could not find constructor")
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

  def case_(
      typ: Type
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]): Parser[((Fun, Expr), Proof), Token] =
    P("case" ~ name ~>@ constargs(typ) ~ "=>" ~@ { case (fun, expr) =>
      proof(scope ++ expr.free.asScope, ctx)
    })

  def cases(
      tactic: Induction
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]): Parser[List[(Sel, Proof)], Token] =
    braces(case_(tactic.x.typ).map { case ((fun, expr), proof) =>
      (ConstrSel(fun, expr.free.toList), proof)
    }.+) | ret(Nil)

  def induction(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Proof("induction" ~ Induction(var_) ~@ cases));

  def maybe_proof(
      phi: Expr
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("proof" ~ scoped_proof(phi)).?

  // SPLIT
  def split_case_(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[(Sel, Proof), Token] =
    P("case" ~ IndexSel(int_) ~ "=>" ~ proof)

  def split_cases(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[List[(Sel, Proof)], Token] =
    braces(split_case_.+) | ret(Nil)

  def split(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(Proof("split" ~ ret(Split) ~ split_cases))

  def subproofs(
      phi: Expr
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    def collect_all_the_vars(phi: Expr): List[Var] = phi match {
      case Forall(bound, body) =>
        bound ++ collect_all_the_vars(body)
      case _ =>
        Nil
    }

    val xs = collect_all_the_vars(phi)
    proof(scope ++ xs.asScope, ctx)
  }

  // SHOW
  def show(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      Proof(
        Show("show" ~ formula)
          ~@ maybe_proof_sel
      )
    )

  def maybe_proof_sel(
      tactic: Show
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]): Parser[List[(Sel, Proof)], Token] =
    P("proof" ~ ret(ProofSel) ~ scoped_proof(tactic.expression) ~ then_sel) map {
      case (sel ~ proof) ~ rest => (sel, proof) :: rest
    }

  def then_sel(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[List[(Sel, Proof)], Token] =
    P(("then" ~ ret(ThenSel) ~ proof).+ | ret(Nil))

  // UNFOLD
  def unfold(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(
      Proof(
        Unfold(
          "unfold" ~ make_fun_ref(
            name ~ ("[" ~ int_ ~ "]").?
          ) ~ ("at" ~ (int_ ~+ ",")).?
        )
          ~ "then" ~ (ret(ThenSel) ~ proof).+
      )
    )

  // AUTO
  def auto(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    "auto" ~ Proof(ret(Auto) ~ ret(Nil))

  // NOAUTO
  def noauto(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("noauto" ~ Proof(ret(NoAuto) ~ (ret(ProofSel) ~ proof).+))

  // BREAKPOINT
  def breakpoint(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    "break" ~ Proof(ret(BreakPoint) ~ ret(Nil))

  // ANY TACTIC
  def proof(implicit
      scope: Map[Name, Var],
      ctx: Map[Name, Param]
  ): Parser[Proof, Token] =
    P(sorry | show | auto | noauto | unfold | induction | breakpoint | split);

  def scoped_proof(
      phi: Expr
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    def collect_all_the_vars(phi: Expr): List[Var] = phi match {
      case Forall(bound, body) =>
        bound ++ collect_all_the_vars(body)
      case _ =>
        Nil
    }

    val xs = collect_all_the_vars(phi)
    proof(scope ++ xs.asScope, ctx)
  }

  def as_kw =
    (name: Name) => sexpr.Kw(name.name)

  def attr =
    P(as_kw(name) ~ ret(None))

  def attrs =
    P("{" ~ ":" ~ (attr ~* ",") ~ "}")

  def maybe_attrs =
    P(attrs | ret(Nil))

  def with_gens[A](
      p: (Map[Name, Var], Map[Name, Param]) => Parser[A, Token]
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(gens ~>@ (params => p(scope, ctx ++ Map(params.names zip params: _*))))

  def formula_with_maybe_proof(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(formula ~@ maybe_proof)

  def lemma_(
      mode: Option[cuvee.smtlib.Mode]
  )(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P(make_lemma(ret(mode) ~ maybe_attrs ~ with_gens(formula_with_maybe_proof(_, _)) ~ ";"))

  def lemma(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("lemma" ~ lemma_(None))

  def free_lemma(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("free lemma" ~ lemma_(Some(Free)))

  def goal(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) =
    P("goal" ~ lemma_(Some(Goal)))

  def datadef_(kw: String, declare: Boolean) =
    (kw ?~ name ?~ gens ?~ "=") ~@ constrs(declare)

  val datadef =
    P(make_datatype(datadef_("data", declare = true) ~ ";"))

  val abstraction =
    P(make_abstraction(datadef_("abstractions", declare = true) ~ ";"))

  def datadefs_(sorts: List[(Name, List[Param])]) = {
    for ((dt, params) <- sorts) {
      val arity = params.length
      state.con(dt, arity)
    }

    P(datadef_("where", declare = false).*)
  }

  val datadefs =
    P(make_datatypes("data" ~ ((name ~ gens) ~+ ",") ~>@ datadefs_ ~ ";"))

  val abstractions =
    P(make_abstractions("abstractions" ~ ((name ~ gens) ~+ ",") ~>@ datadefs_ ~ ";"))

  val fail =
    easyparse.Parser.Fail[Token](hard = true)

  def cmd(implicit scope: Map[Name, Var], ctx: Map[Name, Param]) = {
    val sig = sortdef | datadef | datadefs | constdef | vardecl
    val cl = abstraction | abstractions | contractdef
    val df = fundef | procdef | contractdef
    val ax = axiom | lemma | free_lemma | goal

    P(sig | cl | df | ax | fail)
  }

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
}

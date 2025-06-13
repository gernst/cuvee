package cuvee.simplify

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.pipe.Stage
import cuvee.util.Matching

object Simplify extends Stage {
  import Context.assuming

  def simplify(cmds: List[Cmd], state: State, polarity: Option[Boolean], expr: Expr): Expr = {
    val rules = Rewrite.from(cmds, state)
    println("using rewrite rule:")
    for (eq <- rules)
      println("  " + eq)
    println()

    simplify(polarity, rules.groupBy(_.fun), state.constrs, expr)
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] = {
    cmds flatMap {
      case cmd @ Lemma(expr, tactic, Some(Goal), label) =>
        simplify(prefix ++ cmds, state, Some(true), expr) match {
          case True  => List()
          case expr_ => List(Lemma(expr_, tactic, Some(Goal), label))
        }

      case cmd @ Assert(Not(expr)) =>
        simplify(prefix ++ cmds, state, Some(true), expr) match {
          case True  => List()
          case expr_ => List(Assert(Not(expr_)))
        }

      case cmd =>
        List(cmd)
    }
  }

  def simplify(
      polarity: Option[Boolean],
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun],
      expr: Expr
  ): Expr = {
    simplify(polarity, expr.free, Set(), List(), List(), Map(), Map(), rules, constrs, expr)
  }

  def goal(rules: Map[Fun, List[Rule]], constrs: Set[Fun], expr: Expr): Expr = {
    simplify(Some(true), expr.free, Set(), List(), List(), Map(), Map(), rules, constrs, expr)
  }

  def sequent(rules: Map[Fun, List[Rule]], constrs: Set[Fun], expr: Expr): Expr = {
    simplify(Some(false), expr.free, Set(), List(), List(), Map(), Map(), rules, constrs, expr)
  }

  def repeat[A](a: A)(f: A => A): A = {
    a match {
      case expr: Expr =>
        println()
        println("========== simplify ==========")
        for (line <- cuvee.boogie.printer.lines(Goal(expr)))
          println(line)
        println()
      case _ =>
        println()
        println("========== simplify ==========")
        println(a)
        println()
    }

    val a_ = f(a)
    if (a_ == a) {
      a
    } else {
      repeat(a_)(f)
    }
  }

  def simplify(
      polarity: Option[Boolean],
      fixed: Set[Var],
      arbitrary: Set[Var],
      pos: List[Expr],
      neg: List[Expr],
      su: Map[Var, Expr],
      eq: Map[Var, Expr],
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun],
      expr: Expr
  ): Expr = {
    val ctx = Context(polarity, fixed, arbitrary, pos, neg, su, eq, rules, constrs)
    // repeating at top-level rather than on individual subterms seems more efficient
    // maybe we can even memoize simplify(_, _) but that would speed up the last round only
    repeat(expr) { simplify(ctx, _) }
  }

  def nary(ctx: Context, done: List[Expr], todo: List[Expr], flip: Boolean): List[Expr] = {
    // println("done")
    // for(phi <- done) println("  " + phi)
    // println("todo")
    // for(phi <- todo) println("  " + phi)
    todo match {
      case Nil =>
        done

      case phi :: rest =>
        // println("looking at: " + phi)
        // mildly inelegant, but at least clear
        val pos = if (flip) Nil else done ++ rest
        val neg = if (flip) done ++ rest else Nil

        // Note: should not flip polarity, x must be treated the same in the following two scenarios
        // ==> exists x :: x == e || B
        // ==> exists x :: x == e && B
        val phi_ = simplify(assuming(ctx, pos, neg), phi)
        nary(ctx, done ++ List(phi_), rest, flip)
    }
  }

  def simplify_and(ctx: Context, phis: List[Expr]): List[Expr] = {
    //   println("pos")
    // for(phi <- ctx.pos) println("  " + phi)
    // println("neg")
    // for(phi <- ctx.neg) println("  " + phi)
    nary(ctx, done = Nil, todo = phis, flip = false)
  }

  def simplify_or(ctx: Context, phis: List[Expr]): List[Expr] = {
    // println("disjunction: " + phis)
    nary(ctx, done = Nil, todo = phis, flip = true)
  }

  def simplify(ctx: Context, exprs: List[Expr]): List[Expr] = {
    for (expr <- exprs)
      yield simplify(ctx, expr)
  }

  def simplify_leteqs(ctx: Context, eqs: List[LetEq]): List[LetEq] = {
    for (LetEq(x, expr) <- eqs)
      yield LetEq(x, simplify(ctx, expr))
  }

  def simplify(ctx: Context, init: Expr): Expr = {
    // println("looking at: " + init)
    // println("bound:    " + ctx.free)
    // println("clausify: " + init)
    var expr = Clause.goal(ctx.vars, init)
    // println("       ~> " + expr)

    expr = canon(ctx.recurse, expr)
    expr = rewrite(ctx.recurse, expr)

    if (ctx.pos contains expr) {
      True
    } else if (ctx.neg contains expr) {
      False
    } else if (expr == init) {
      init
    } else {
      // don't run again here! could come in with different context
      // println("step " + init)
      // println("  ~> " + expr)
      // println()
      // simplify(ctx.again, expr)

      expr
    }
  }

  def canon(ctx: Context, expr: Expr): Expr = {
    expr match {
      case Eq(left, right) =>
        val left_ = simplify(ctx, left)
        val right_ = simplify(ctx, right)
        eq(ctx, left_, right_)

      case Ge(left, right) => le(ctx, simplify(ctx, right), simplify(ctx, left))
      case Gt(left, right) => lt(ctx, simplify(ctx, right), simplify(ctx, left))

      case Not(Ge(left, right)) => lt(ctx, simplify(ctx, left), simplify(ctx, right))
      case Not(Gt(left, right)) => le(ctx, simplify(ctx, left), simplify(ctx, right))
      case Not(Le(left, right)) => lt(ctx, simplify(ctx, right), simplify(ctx, left))
      case Not(Lt(left, right)) => le(ctx, simplify(ctx, right), simplify(ctx, left))

      case Not(phi) =>
        val phi_ = simplify(ctx.flip, phi)
        not(phi_)

      case Imp(phi, psi) =>
        val phi_ = simplify(assuming(ctx.flip, neg = List(psi)), phi)
        val psi_ = simplify(assuming(ctx, pos = List(phi_)), psi)
        imp(phi_, psi_)

      // case Eq(phi, psi) if phi.typ == Sort.bool =>
      // A /\ B <==> A /\ C should not just simplify sides under assumptions!
      //   val phi_ = simplify(assuming(ctx, pos = List(psi)), phi)
      //   val psi_ = simplify(assuming(ctx, pos = List(phi_)), psi)
      //   eq(phi_, psi_)

      case Or(phis) =>
        val phis_ = simplify_or(ctx, phis)
        or(phis_)

      case And(phis) =>
        val phis_ = simplify_and(ctx, phis)
        and(phis_)

      case expr @ Forall(formals, body) =>
        require(expr.bound disjoint ctx.vars, "variables already bound: " + (expr.bound & ctx.vars))
        val body_ = simplify(ctx forall formals, body)
        forall(formals, body_)

      case expr @ Exists(formals, body) =>
        require(expr.bound disjoint ctx.vars, "variables already bound: " + (expr.bound & ctx.vars))
        val body_ = simplify(ctx exists formals, body)
        exists(formals, body_)

      // --- basic formulas end here ---

      case _ if expr.typ == Sort.int && ctx.arith =>
        // maybe need to enable arith at leaves again
        val expr_ = simplify(ctx.noArith, expr)
        val poly = Poly(expr_)
        poly.compact.toExpr

      case expr @ Let(eqs, body) =>
        require(expr.bound disjoint ctx.vars, "variables already bound: " + (expr.bound & ctx.vars))
        require(ctx.isUnpolar, "unexpected top-level let")
        val eqs_ = simplify_leteqs(ctx, eqs)
        val body_ = simplify(ctx, body)
        let(eqs_, body_)

      case Ite(test, left, right) =>
        val test_ = simplify(ctx.unpolar, test)
        val left_ = simplify(assuming(ctx, pos = List(test_)), left)
        val right_ = simplify(assuming(ctx, neg = List(test_)), right)
        val res = ite(test_, left_, right_)
        println(res)
        res

      case Select(base, index) =>
        val base_ = simplify(ctx.unpolar, base)
        val index_ = simplify(ctx.unpolar, index)
        select(base_, index_)

      case Store(base, index, value) =>
        val base_ = simplify(ctx.unpolar, base)
        val index_ = simplify(ctx.unpolar, index)
        val value_ = simplify(ctx.unpolar, value)
        store(base_, index_, value_)

      case App(inst, args) =>
        val args_ = simplify(ctx.unpolar, args)
        App(inst, args_)

      case expr =>
        expr
    }
  }

  def not(phi: Expr): Expr = {
    phi match {
      case False    => True
      case True     => False
      case Not(psi) => psi
      case _        => Not(phi)
    }
  }

  def imp(phi: Expr, psi: Expr): Expr = {
    (phi, psi) match {
      case (_, True)       => True
      case (False, _)      => True
      case (True, _)       => psi
      case (_, False)      => not(phi)
      case _ if phi == psi => True
      case _               => Imp(phi, psi)
    }
  }

  def or(phis: List[Expr]): Expr = {
    val phis_ = Or.flatten(phis)
    if (phis_ contains True) True
    else Or(phis_.distinct filter (_ != False))
  }

  def and(phis: List[Expr]): Expr = {
    val phis_ = And.flatten(phis)
    if (phis_ contains False) False
    else And(phis_.distinct filter (_ != True))
  }

  def let(eqs: List[LetEq], body: Expr): Expr = {
    val eqs_ = eqs filter (body.free contains _.x)
    if (eqs_.isEmpty) body
    else Let(eqs_, body)
  }

  def forall(bound: List[Var], psi: Expr): Expr = {
    Forall(bound, psi) // simplified by quant.apply already
  }

  def exists(bound: List[Var], psi: Expr): Expr = {
    Exists(bound, psi) // simplified by quant.apply already
  }

  def ite(test: Expr, left: Expr, right: Expr) = {
    (test, left, right) match {
      case _ if left == right => left
      case (True, _, _)       => left
      case (False, _, _)      => right
      case (_, _, True)       => imp(test, left)
      case (_, True, _)       => imp(not(test), right)
      case (_, _, False)      => and(List(test, left))
      case (_, False, _)      => and(List(not(test), right))
      // case _ if test == left  => or(List(test, right)) // XXX: too specific! should have left == True then from context
      // case _ if test == right => or(List(test, left))
      case _ => Ite(test, left, right)
    }
  }

  def canInstantiate(ctx: Context, x: Var) = {
    ctx.polarity match {
      case Some(true) =>
        ctx.bound contains x

      case Some(false) =>
        ctx.fixed contains x

      case None =>
        false
    }
  }

  def eq(ctx: Context, left: Expr, right: Expr): Expr = {
    (left, right) match {
      case (phi, True)        => phi
      case (True, psi)        => psi
      case (False, psi)       => not(psi)
      case (phi, False)       => not(phi)
      case _ if left == right => True

      case (Lit(left, _), Lit(right, _)) =>
        assert(left != right) // checked above!
        False

      case (x: Var, _)
          if !(right.free contains x) && !(ctx.free contains x) && canInstantiate(ctx, x) =>
        // println("dropping " + x + " == " + right)
        True

      // case _ if left.typ == Sort.int && right.typ == Sort.int =>
      //   ???

      /* TODO: add proper solver for ADTs
      case (App(Inst(f, _), la), App(Inst(g, _), ra))
          if (constrs contains f) && (constrs contains g) =>
        if (f == g) {
          // unpack arguments as equations
          val eqs =
            for ((l, r) <- (la zip ra))
              yield eq(l, r)
          and(eqs)
        } else {
          // data types are freely generated, so constructors never overlap
          False
        }

      case (App(Inst(f, _), la), r) if (constrs contains f) && (la contains r) =>
        False

      case (l, App(Inst(g, _), ra)) if (constrs contains g) && (ra contains l) =>
        False
       */

      case _ =>
        Eq(left, right)
    }
  }

  def le(ctx: Context, left: Expr, right: Expr) = {
    Le(left, right)
  }

  def lt(ctx: Context, left: Expr, right: Expr) = {
    Lt(left, right)
  }

  def select(base: Expr, index: Expr): Expr = {
    (base, index) match {
      case (Store(_, `index`, value), _) =>
        value

      case (Store(base_, Lit(any_, _), value), Lit(any, _)) if any != any_ =>
        val intermediate = Select(base_, index)
        select(base_, index)

      case (Bind(Quant.lambda, List(x), body, _), _) =>
        val su = Expr.subst(x -> index)
        body subst su

      case _ =>
        Select(base, index)
    }
  }

  def store(base: Expr, index: Expr, value: Expr): Expr = {
    (base, index, value) match {
      case (_, _, Select(`base`, `index`)) =>
        base
      case (Store(base_, `index`, _), _, _) =>
        val intermediate = Store(base, index, value)
        store(base_, index, value)
      case _ =>
        Store(base, index, value)
    }
  }

  def rewrite(ctx: Context, expr: Expr): Expr = {
    // println("rewriting " + expr)
    // println()

    // val su = Context.eqs(ctx)
    val expr_ = expr subst ctx.su

    expr_ match {
      case Le(Lit(m: BigInt, _), Lit(n: BigInt, _)) =>
        if (m <= n) True else False
      case Lt(Lit(m: BigInt, _), Lit(n: BigInt, _)) =>
        if (m < n) True else False

      case Le(left, right) if ctx.pos contains Le(right, left) =>
        Eq(left, right)

      case Le(left, right) if ctx.pos contains Lt(left, right) =>
        True
      case Le(left, right) if ctx.pos contains Lt(right, left) =>
        False
      case Lt(left, right) if ctx.pos contains Lt(right, left) =>
        False
      case Le(left, right) if left == right =>
        True

      case App(inst, args) if ctx.rules contains inst.fun =>
        val use = ctx.rules(inst.fun)
        ???
        // rewrite(ctx, use, expr_)

      case _ =>
        expr_
    }
  }

/*
  def rewrite(ctx: Context, use: List[Rule], expr: Expr): Expr = {
    use match {
      case Nil =>
        expr

      case eq :: rest =>
        // println("applying rule: " + eq)
        // println("to " + expr)
        rewrite(ctx, eq, rest, expr)
    }
  }

  def rewrite(ctx: Context, eqn: Rule, use: List[Rule], expr: Expr): Expr = {
    val Rule(pat, rhs, cond, avoid) = eqn.gen

    import Bnd._

    try {
      val xs = ctx.free ++ expr.free // need both!
      val ys = pat.free ++ cond.free // need both!
      val dep = ys map (x => (x, xs))
      val bn = Bnd(dep.toMap, Set(), Map(), Map(), Map(), List(), Map(), Map())
      val binding = bind("lhs rule", ctx, pat, expr, bn)

      // println("rule matched: " + pat + " at " + expr)
      println()
      println("applying rule: " + eqn)
      println("to " + expr)

      if (cond != True) {
        // println("checking side condition " + cond)
        // for (phi <- ctx.assms)
        //   println("  given: " + phi)
        // for (eq <- ctx.su)
        //   println("  subst: " + eq)
        // for (eq <- ctx.eq)
        //   println("  defn:  " + eq)
      }

      // val cond_ = simplify(ctx, cond)
      // if (cond_ == True) {
      //   println("  success")
      // }

      // println()
      // println("again for rule: " + eq)
      val binding_ = find(ctx, cond, binding)

      // if (cond_ != True) {
      //   throw Rewrite.PremiseNotValid
      // }

      for ((a, b) <- avoid) {
        if (binding_(a) == binding_(b))
          throw Rewrite.InstanceAvoided
      }

      val rhs_ = binding_(rhs)

      println("rewrite " + expr)
      println("    ~ > " + rhs_)

      // XXX: seems good now:
      // require(binding_.tr.isEmpty, "oops, forgot to replace: " + binding_.tr)

      rewrite(ctx.again, rhs_)

    } catch { // this rule does not apply, try other rules
      case Type.CannotBind(pat, arg, ty) =>
        // println("cannot bind " + pat + " to " + arg + " with " + ty)
        rewrite(ctx, use, expr)

      case Expr.CannotBind(pat, arg, ty, su) =>
        // println("cannot bind " + pat + " to " + arg + " with " + ty + " and " + su)
        rewrite(ctx, use, expr)

      case Rewrite.PremiseNotValid | Rewrite.InstanceAvoided =>
        rewrite(ctx, use, expr)
    }
  }
  */
}

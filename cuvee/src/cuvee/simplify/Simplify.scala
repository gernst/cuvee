package cuvee.simplify

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.pipe.Stage
import cuvee.util.Matching
import cuvee.imp.traces.Trace
import cuvee.imp.traces.Update
import cuvee.imp.traces.Mapping
import cuvee.imp.annotate.Traces
import cuvee.imp.traces.Invariant

object Simplify extends Stage {
  import Context.assuming

  def simplify(cmds: List[Cmd], state: State, polarity: Option[Boolean], expr: Expr): Expr = {
    val rules = Rewrite.from(cmds, state, split = false)
    // println("using rewrite rules:")
    // for (eq <- rules)
    //   println("  " + eq)
    // println()

    val rws = rules.groupBy(_.fun)
    simplify(polarity, rws, state.constrs, expr)
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] = {
    cmds flatMap {
      case cmd @ Lemma(expr, tactic, Some(Free), label) =>
        List(cmd)

      case cmd @ Lemma(expr, tactic, mode, label) =>
        simplify(prefix ++ cmds, state, Some(true), expr) match {
          case True =>
            List()
          case Clause(xs, ant, Note(suc, pattern, attrs)) =>
            val expr_ = Clause(xs, ant, suc)
            List(Lemma(expr_, tactic, mode, label ++ attrs))
          case expr_ =>
            List(Lemma(expr_, tactic, mode, label))
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
    // a match {
    //   case expr: Expr =>
    //     println()
    //     println("========== simplify ==========")
    //     for (line <- cuvee.boogie.printer.lines(Goal(expr)))
    //       println(line)
    //     println()
    //   case _ =>
    //     println()
    //     println("========== simplify ==========")
    //     println(a)
    //     println()
    // }

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
        // println("looking at: " + phi + " with rest: " + rest)
        // mildly inelegant, but at least clear
        val pos = if (flip) Nil else done ++ rest
        val neg = if (flip) done ++ rest else Nil

        // Note: should not flip polarity, x must be treated the same in the following two scenarios
        // ==> exists x :: x == e || B
        // ==> exists x :: x == e && B
        val ctx_ = assuming(ctx, pos, neg)
        // println("context assumptions: " + ctx_)
        val phi_ = simplify(ctx_, phi)
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
    // println("given:      " + ctx.assms)
    // println("bound:      " + ctx.bound)
    // println("fixed:      " + ctx.fixed)
    // println()

    // println("clausify: " + init)
    // XXX: applied to ANY expression, not just bool
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
      for (eq <- ctx.su)
        println("su   " + eq)
      for (eq <- ctx.eq)
        println("eq   " + eq)
      for (phi <- ctx.assms)
        println("assm " + phi)
      println("step " + init)
      println("  ~> " + expr)
      println()
      // simplify(ctx.again, expr)

      expr
    }
  }

  def canon(ctx: Context, expr: Expr): Expr = {
    expr match {
      case Note(True, _, _)  => True
      case Note(False, _, _) => False

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
        Poly.simplify(expr_)

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

      case expr: Invariant =>
        val Invariant(formals, cond) = expr refresh ctx.vars
        val ctx_ = ctx.unpolar
        val phis = And.flattenStrong(cond)
        val invs =
          for (phi <- phis)
            yield {
              val xs = phi.free
              val eqs = formals filter { xs contains _.x }

              val eqs_ = simplify_leteqs(ctx_, eqs)
              val phi_ = simplify(ctx, phi)
              Invariant(eqs_, phi_)
            }

        And(invs)

      case expr: Mapping =>
        val Mapping(formals, result) = expr refresh ctx.vars
        val ctx_ = ctx.unpolar
        // XXX: how does that not crash with unbound variables?
        val formals_ = simplify_leteqs(ctx_, formals)
        val result_ = simplify(ctx, result)
        Mapping(formals_, result_)

      case expr: Trace =>
        val Trace(init, formals, acc, updates) = expr refresh ctx.vars
        val ctx_ = ctx.unpolar
        // XXX: how does that not crash with unbound variables?
        val init_ = simplify(ctx_, init)
        val formals_ = simplify_leteqs(ctx_, formals)
        val updates_ = simplify_updates(ctx_, formals_, updates)
        Trace(init_, formals_, acc, updates_)

      case expr =>
        expr
    }
  }

  def simplify_updates(
      ctx: Context,
      formals_ : List[LetEq],
      updates: List[Update]
  ): List[Update] = {
    // TODO: earlier or current?
    //       probably earlier, because all current is with respect to the external counter k
    //       but also the problem is that they are not viewed jointly from an earlier state!!
    //       here should introduce another counter for the earlier state
    // val assms =
    //   for (LetEq(x, e) <- iteration_.formals)
    //     yield simplify(ctx, Traces.Current(x, e))

    val assms = Nil

    val ctx_ = assuming(ctx, pos = assms)

    val updates_ =
      for (Update(path, rhs) <- updates) yield {
        // argh below very inelegant
        val path_ = simplify(ctx_, path)
        val rhs_ = simplify(assuming(ctx_, pos = List(path_)), rhs)
        Update(path_, rhs_)
      }

    updates_.filterNot(_.path == False)
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
          if !(right.free contains x) && !(ctx.free contains x) && (ctx canInstantiate x) =>
        True

      // case _ if left.typ == Sort.int && right.typ == Sort.int =>
      //   ???

      // TODO: add proper solver for ADTs
      case (App(Inst(f, _), la), App(Inst(g, _), ra))
          if (ctx.constrs contains f) && (ctx.constrs contains g) =>
        if (f == g) {
          // unpack arguments as equations
          val eqs =
            for ((l, r) <- (la zip ra))
              yield eq(ctx, l, r)
          and(eqs)
        } else {
          // data types are freely generated, so constructors never overlap
          False
        }

      case (App(Inst(f, _), la), r) if (ctx.constrs contains f) && (la contains r) =>
        False

      case (l, App(Inst(g, _), ra)) if (ctx.constrs contains g) && (ra contains l) =>
        False

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
    // println("rewriting " + expr + " in " + ctx)

    // val su = Context.eqs(ctx)
    val expr_ = expr subst ctx.su
    // println(expr_)
    // println()

    expr_ match {
      case Le(Lit(m: BigInt, _), Lit(n: BigInt, _)) =>
        if (m <= n) True else False
      case Lt(Lit(m: BigInt, _), Lit(n: BigInt, _)) =>
        if (m < n) True else False
      case DivBy(Lit(m: BigInt, _), Lit(n: BigInt, _)) =>
        Lit(m / n, Sort.int)

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

      // case Current(Mapping(iteration, result)) =>
      //   val su = Expr.subst(
      //     for (LetEq(y, ys) <- iteration.formals)
      //       yield y -> Current(ys)
      //   )

      //   result subst su

      case App(inst, args) if ctx.rules contains inst.fun =>
        val use = ctx.rules(inst.fun)
        rewrite(ctx, use, expr_)

      case _: Mapping if ctx.rules contains Fun.map =>
        val use = ctx.rules(Fun.map)
        rewrite(ctx, use, expr_)

      case _: Invariant if ctx.rules contains Fun.inv =>
        val use = ctx.rules(Fun.inv)
        rewrite(ctx, use, expr_)

      case _: Trace if ctx.rules contains Fun.trace =>
        val use = ctx.rules(Fun.trace)
        rewrite(ctx, use, expr_)

      case _ =>
        expr_
    }
  }

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

    try {
      val (ty, su) = bind(ctx, pat, expr)

      // XXX: check if the instance is partial
      val _cond = simplify(ctx, cond inst (ty, su))

      if (_cond != True) {
        throw Rewrite.PremiseNotValid // ("side-condition not satisfied " + _cond)
      }

      for ((a, b) <- avoid) {
        if ((a inst (ty, su)) == (b inst (ty, su)))
          throw Rewrite.InstanceAvoided
      }

      val rhs_ = rhs inst (ty, su)

      rewrite(ctx.again, rhs_)

    } catch { // this rule does not apply, try other rules
      case Type.CannotBind(pat, arg, ty) =>
        // println("cannot bind " + pat + " to " + arg + " with " + ty)
        rewrite(ctx, use, expr)

      case Expr.CannotBind(pat, arg, ty, su, reason) =>
        // println(
        //   "cannot bind " + pat + " to " + arg + " with " + ty + " and " + su + " (" + reason + ")"
        // )
        rewrite(ctx, use, expr)

      case Rewrite.PremiseNotValid | Rewrite.InstanceAvoided =>
        rewrite(ctx, use, expr)
    }
  }

  def bind(
      ctx: Context,
      pat: Expr,
      arg: Expr,
      ty: Map[Param, Type] = Map(),
      su: Map[Var, Expr] = Map()
  ): (Map[Param, Type], Map[Var, Expr]) = {
    // println("binding")
    // println("pat: " + pat)
    // println("arg: " + arg)

    (pat, arg) match {
      case (x: Var, _) if su contains x =>
        if (su(x) != arg) {
          // println("cannot bind " + pat + " to " + arg + " with " + ty + " and " + su)
          throw Expr.CannotBind(pat, arg, ty, su, "not equal")
        }

        (ty, su)

      case (x: Var, _) =>
        val ty_ = Type.bind(x.typ, arg.typ, ty)
        (ty_, su + (x -> arg))

      case (a: Lit, b: Lit) if a == b =>
        (ty, su)

      // follow non-substituted equation
      case (_, y: Var) if ctx.eq contains y =>
        bind(ctx, pat, ctx eq y, ty, su)

      case (App(inst1, pats), App(inst2, args)) if inst1.fun == inst2.fun =>
        val ty_ = Type.binds(inst1.args, inst1.res, inst2.args, inst2.res, ty)
        val (ty__, su_) = bind(ctx, pats, args, ty_, su)
        (ty__, su_)

      case (map: Mapping, Mapping(formals2, result2)) =>
        val pat @ Mapping(formals1, result1) = map.gen
        val tr2 = formals2.asMap

        var (ty1, su1) =
          bind(ctx, result1, result2, ty, su)

        val uncaptured =
          formals2.vars.toSet & result2.free

        if (uncaptured.nonEmpty)
          throw Expr.CannotBind(pat, arg, ty, su, "uncaptured: " + uncaptured)

        val iteration =
          cover2(formals1, formals2, (ty1, su1)) { case (eq1, formals2, (ty4, su4)) =>
            find(ctx, eq1, formals2, tr2, ty4, su4)
          }

        first(pat, arg, ty, su, iteration)

      case (inv: Invariant, Invariant(formals2, cond2)) =>
        val pat @ Invariant(formals1, cond1) = inv.gen
        val tr2 = formals2.asMap

        var (ty1, su1) =
          bind(ctx, cond1, cond2, ty, su)

        val uncaptured =
          formals2.vars.toSet & cond2.free

        if (uncaptured.nonEmpty)
          throw Expr.CannotBind(pat, arg, ty, su, "uncaptured: " + uncaptured)

        val iteration =
          cover2(formals1, formals2, (ty1, su1)) { case (eq1, formals2, (ty4, su4)) =>
            find(ctx, eq1, formals2, tr2, ty4, su4)
          }

        first(pat, arg, ty, su, iteration)

      case (trace: Trace, Trace(init2, formals2, acc2, updates2)) =>
        val pat @ Trace(init1, formals1, acc1, updates1) = trace.gen
        val tr2 = formals2.asMap

        // we can just bind the accumulator and ignore to remove it,
        // because the left-hand side of the rule is completely fresh
        var (ty1, su1) =
          bind(ctx, List(init1, acc1), List(init2, acc2), ty, su)

        // cover every actual update: the rule must be applicable to each possible transition of the iteration
        val updates =
          cover(updates2, updates1, (ty1, su1)) { case (up2, up1, (ty2, su2)) =>
            val uncaptured =
              formals2.vars.toSet & up2.free

            if (uncaptured.nonEmpty)
              throw Expr.CannotBind(pat, arg, ty, su, "uncaptured: " + uncaptured)

            bind(ctx, up1, up2, ty2, su2)
          }

        // the goal is to then cover all *trace* variables occurring in the iteration of the pattern,
        // however, we first leverage that we have a mapping for some *local* bindings,
        // and then try to figure out the rest
        val iteration =
          for ((ty3, su3) <- updates)
            yield cover2(formals1, formals2, (ty3, su3)) { case (eq1, formals2, (ty4, su4)) =>
              find(ctx, eq1, formals2, tr2, ty4, su4)
            }

        first(pat, arg, ty, su, iteration.flatten)

      case _ =>
        throw Expr.CannotBind(pat, arg, ty, su, "incompatible")
    }
  }

  def first(
      pat: Expr,
      arg: Expr,
      ty: Map[Param, Type],
      su: Map[Var, Expr],
      results: List[(Map[Param, Type], Map[Var, Expr])]
  ) = {
    results.distinct match {
      case Nil =>
        throw Expr.CannotBind(pat, arg, ty, su, "no intermediate results")

      case List((ty_, su_)) =>
        (ty_, su_)

      case results =>
        // bad setup of rewrite theory?
        // could potentially happen, for example with
        // current(_, range(0, 1, n))
        // current(_, range(0, c, n))

        // but maybe fix the later one with avoiding c -> 1
        for ((ty_, su_) <- results) {
          println("  " + ty_ + " " + su_)
        }
        cuvee.error("multiple for iteration matches of " + pat + " for " + arg)
    }
  }

  def bind(
      ctx: Context,
      pat: Update,
      arg: Update,
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pat, arg) match {
      case (Update(path1, rhs1), Update(path2, rhs2)) =>
        val (ty_, su_) = bind(ctx, rhs1, rhs2, ty, su)
        val ctx_ = assuming(ctx, pos = List(path2))

        val results = find(ctx_, path1, ty_, su_)

        // hack due to find reeturning the same match many times
        // for conditions that have no further variables to be matched
        results.distinct match {
          case List(res) =>
            res

          case Nil =>
            throw Expr.CannotBind(path1, path2, ty_, su_, "not found")

          case results =>
            cuvee.error("multiple matches for update guard: " + results)
        }
    }
  }

  def bind(
      ctx: Context,
      pats: List[Expr],
      args: List[Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): (Map[Param, Type], Map[Var, Expr]) = {
    (pats, args) match {
      case (Nil, Nil) =>
        (ty, su)

      case (pat :: pats, arg :: args) =>
        val (ty_, su_) = bind(ctx, pat, arg, ty, su)
        bind(ctx, pats, args, ty_, su_)
    }
  }

  def find(
      ctx: Context,
      pat: LetEq,
      formals: List[LetEq],
      tr: Map[Var, Expr],
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): List[(Map[Param, Type], Map[Var, Expr])] = {
    pat match {
      case LetEq(x1, xs1: Var) if su contains x1 =>
        // require(!(su4 contains xs1), "trace already bound from update " + xs1)

        su(x1) match {
          // pattern iteration variable x1 is bound just to a simple variable x2
          // then just map xs1 to the corresponding trace xs2 (special case)
          case x2: Var if tr contains x2 =>
            List(bind(ctx, xs1, tr(x2), ty, su))

          case e2 =>
            val ys = e2.free
            val formals_ = formals.filter { case LetEq(x, e) => // XXX: big hack! keep counter here
              (x.name.name startsWith "#") || (ys contains x)
            }

            require(ys.nonEmpty, "uh oh generating trace without dependencies")

            // println(xs1 + " -> map(" + formals_ + " yield " + e2 + ")")
            List(bind(ctx, xs1, Mapping(formals_, e2), ty, su))
        }

      case LetEq(x1, xs1) =>
        // println("looking for " + xs1 + " among " + formals)
        cover(xs1, formals.args, (ty, su)) { case (pat, arg, (ty_, sy_)) =>
          bind(ctx, pat, arg, ty_, sy_)
        }
    }
  }

  def find(
      ctx: Context,
      phi: Expr,
      ty: Map[Param, Type],
      su: Map[Var, Expr]
  ): List[(Map[Param, Type], Map[Var, Expr])] = {
    val phis = And.flattenStrong(phi) // ensure absence of true here
    // println("finding:  " + phis)
    // println("given su: " + su)
    // println("context:  " + ctx.assms)

    // TODO: pick those from phis first which have no free variables,
    //       currently results end up many times
    cover(phis, ctx.assms, (ty, su)) {
      case (phi, assm, (ty, su)) if phi.free subsetOf su.keySet =>
        val phi_ = simplify(ctx, phi inst (ty, su))
        if (phi_ == True) {
          // println("found " + phi + " == true ")
          (ty, su)
        } else {
          // println("not found " + phi + " != true ")
          throw Expr.CannotBind(assm, phi, ty, su, "not covered")
        }

      case (phi, assm, (ty, su)) =>
        // println("bind? " + (phi inst (ty, su)) + " == " + assm)
        val res = bind(ctx, phi, assm, ty, su)
        // println("found " + phi + " == " + assm)
        res
    }
  }

  // for all bs find some matching as
  def cover[A, B, S](as: List[A], bs: List[B], s: S)(
      f: (A, B, S) => S
  ): List[S] = as match {
    case Nil =>
      List(s)

    case a :: as =>
      for (
        s_ <- cover(a, bs, s)(f);
        s__ <- cover(as, bs, s_)(f)
      )
        yield (s__)
  }

  def cover[A, B, S](a: A, bs: List[B], s: S)(
      f: (A, B, S) => S
  ): List[S] = bs match {
    case Nil =>
      Nil

    case b :: bs =>
      val here =
        try {
          List(f(a, b, s))
        } catch {
          case e: Type.CannotBind => println(e); Nil
          case e: Expr.CannotBind => println(e); Nil
        }

      val there =
        cover(a, bs, s)(f)

      here ++ there
  }

  // for all bs find some matching as
  def cover2[A, B, S](as: List[A], bs: List[B], s: S)(
      f: (A, List[B], S) => List[S]
  ): List[S] = as match {
    case Nil =>
      List(s)

    case a :: as =>
      for (
        s_ <- f(a, bs, s);
        s__ <- cover2(as, bs, s_)(f)
      )
        yield (s__)
  }
}

package cuvee.imp

import cuvee.error
import cuvee.pure._
import cuvee.State
import cuvee.pipe.Stage
import cuvee.smtlib._
import cuvee.imp.transform.Inline
import cuvee.sexpr.Id
import cuvee.sexpr.Kw
import cuvee.imp.traces._
import cuvee.sexpr.Parser.sexpr

class VCGenStage(partial: Boolean) extends Stage {
  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) = {
    val eval = new VCGen(state)

    cmds flatMap {
      case Assert(expr) =>
        List(Assert(eval.eval(expr)))

      case Lemma(expr, tactic, mode, label) =>
        List(Lemma(eval.eval(expr), tactic, mode, label))

      case DefineFun(name, params, formals, res, body, rec) =>
        val scope = Expr.id(formals)
        List(DefineFun(name, params, formals, res, eval.eval(body, scope), rec))

      case DeclareVar(_, _) =>
        Nil

      case DeclareProc(name, params, in, out, spec) =>
        Nil

      case DefineProc(name, params, in, out, None, body) =>
        val su = Expr.subst(in, Old(in))
        val xs = in ++ out

        val scope: Map[Var, Var] = Map()
        val st = Expr.id(xs)
        val old = List(st)

        val how = if (partial) Box else WP

        val phi = Forall(xs, eval.wp_proc(how, body, scope, st, True))
        // val phi_ = Simplify.simplify(phi, Map(), state.constrs)
        List(Goal(phi))

      case DefineProc(name, params, in, out, Some(Spec(globals, pre, post)), body) =>
        val su = Expr.subst(in, Old(in))
        val xs = in ++ out ++ globals
        val post_ = post subst su

        val scope: Map[Var, Var] = Map()
        val st = Expr.id(xs)
        val old = List(st)

        val how = if (partial) Box else WP

        val phi = Forall(xs, pre ==> eval.wp_proc(how, body, scope, st, post_))
        // val phi_ = Simplify.simplify(phi, Map(), state.constrs)
        List(Goal(phi))

      case cmd =>
        List(cmd)
    }
  }
}

class VCGen(val state: State) {
  def eval(
      expr: Expr,
      scope: Map[Var, Var] = Map(),
      st: Map[Var, Expr] = Map(),
      old: List[Map[Var, Expr]] = Nil
  ): Expr = expr match {
    // Note: must take from scope first!
    //       binders determine bound variables
    case x: Var if (scope contains x) =>
      scope(x)

    case x: Var if (st contains x) =>
      st(x)

    case x: Var =>
      error(
        "undefined program variable: " + x + " in state " + st.keys.mkString(
          " "
        ) + " and scope " + scope.keys.mkString(" ")
      )

    case _: Lit =>
      expr

    case Is(arg, fun) =>
      Is(eval(arg, scope, st, old), fun)

    case Note(expr, patterns, attr) =>
      val expr_ = eval(expr, scope, st, old)
      val patterns_ = patterns map (evals(_, scope, st, old))
      Note(expr_, patterns_, attr)

    case Old(expr) =>
      require(
        old.nonEmpty,
        "cannot evaluate old expression, no previous state(s) given"
      )
      eval(expr, scope, old.head, old.tail)

    case App(inst, args) =>
      val args_ = args map (eval(_, scope, st, old))
      App(inst, args_)

    case Distinct(args) =>
      val args_ = args map (eval(_, scope, st, old))
      Distinct(args_)

    case expr: Expr.bind[_] =>
      val expr_ = expr refresh Expr.free(st)
      val scope_ = scope ++ Expr.id(expr_.bound)

      expr_ match {
        case Bind(quant, xs, body, typ) =>
          val body_ = eval(body, scope_, st, old)
          Bind(quant, xs, body_, typ)

        case Let(eqs, body) =>
          val eqs_ = evalq(eqs, scope, st, old)
          val body_ = eval(body, scope_, st, old)
          Let(eqs_, body_)
      }

    case expr: Expr.bind2[_] =>
      val expr_ = expr refresh Expr.free(st)
      val scope_ = scope ++ Expr.id(expr_.bound)

      expr_ match {
        case Mapping(iteration, result) =>
          val iteration_ = eval(iteration, scope, st, old)
          val result_ = eval(result, scope_, st, old)
          Mapping(iteration_, result_)

        case Trace(init, iteration, acc, updates) =>
          val init_ = eval(init, scope, st, old)
          val iteration_ = eval(iteration, scope, st, old)
          val updates_ = evalu(updates, scope_, st, old)
          Trace(init_, iteration_, acc, updates_)
      }

    case Post(how, prog, post) =>
      wp(how, prog, scope, st, post, old)
  }

  def eval(
      update: Update,
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): Update = {
    val Update(path, rhs) = update
    val path_ = eval(path, scope, st, old)
    val rhs_ = eval(rhs, scope, st, old)
    Update(path_, rhs_)
  }

  def evalu(
      updates: List[Update],
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): List[Update] = {
    for (update <- updates)
      yield eval(update, scope, st, old)
  }

  def eval(
      iteration: Iteration,
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): Iteration = {
    val Iteration(order, formals) = iteration
    val formals_ = evalq(formals, scope, st, old)
    Iteration(order, formals_)
  }
  def evalq(
      eqs: List[LetEq],
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): List[LetEq] = {
    for (LetEq(x, e) <- eqs)
      yield LetEq(x, eval(e, scope, st, old))
  }

  def evals(
      exprs: List[Expr],
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): List[Expr] = {
    for (expr <- exprs)
      yield eval(expr, scope, st, old)
  }

  def havoc(xs: List[Var]) = {
    val re = Expr.fresh(xs)
    val xs_ = xs rename re
    (xs_, re)
  }

  def assign(st: Map[Var, Expr], xs: List[Var], es: List[Expr]) = {
    st ++ (xs zip es)
  }

  type Exit = (Map[Var, Expr], Set[Id], Set[Id]) => Expr

  def no_brk(st: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) =
    cuvee.error("break not within while loop")

  def no_ret(st: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) =
    cuvee.error("return not within procedure")

  def done(
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      live: Set[Id],
      not_live: Set[Id],
      post: Expr,
      old: List[Map[Var, Expr]]
  ) = {
    val post_ = eval(post, scope, st, old)
    post_ source "ensures"
  }

  def wp(
      how: Modality,
      prog: Prog,
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      post: Expr,
      old: List[Map[Var, Expr]] = Nil
  ): Expr = {
    wp(
      how,
      List(prog),
      Nil,
      scope,
      st,
      old,
      Set(),
      Set(),
      done(scope, _, _, _, post, old),
      no_brk(_, _, _),
      no_ret(_, _, _)
    )
  }

  def wp_proc(
      how: Modality,
      prog: Prog,
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      post: Expr
  ): Expr = {
    val old = List(st)

    wp(
      how,
      List(prog),
      Nil,
      scope,
      st,
      old,
      Set(),
      Set(),
      done(scope, _, _, _, post, old),
      no_brk,
      done(scope, _, _, _, post, old)
    )
  }

  def wp(
      how: Modality,
      progs: List[Prog], /* current block */
      cont: List[List[Prog]],
      scope: Map[Var, Var],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]],
      live: Set[Id],
      not_live: Set[Id],
      post: Exit,
      brk: Exit,
      ret: Exit
  ): Expr =
    progs match {
      case Nil =>
        cont match {
          case Nil =>
            post(st, live, not_live)
          case progs :: cont =>
            // Note: no need to cleanup locals from st,
            //       we rename them when we introduce them
            wp(how, progs, cont, scope, st, old, live, not_live, post, brk, ret)
        }

      case cuvee.imp.Note(prog, attrs) :: rest =>
        // TODO: refactor attributes with proper accessors
        val tags = attrs values [Id] "tag"

        val live_ =
          if (attrs contains "live")
            live -- tags
          else
            live

        val not_live_ =
          if (attrs contains "not-live")
            not_live ++ tags
          else
            not_live

        wp(how, rest, cont, scope, st, old, live_, not_live_, post, brk, ret)

      case Block(progs) :: rest =>
        wp(how, progs, rest :: cont, scope, st, old, live, not_live, post, brk, ret)

      case Break :: rest =>
        brk(st, live, not_live)

      case Return :: rest =>
        ret(st, live, not_live)

      case Local(xs, init) :: rest =>
        // Note: ensure we introduce fresh names for the locals
        //       and compute on these within the current block (but not in cont)
        val (ys, zs) = xs partition st.contains
        val (ys_, re) = havoc(ys)
        val xs_ = ys_ ++ zs
        val rest_ = rest replace re
        val init_ = if (init.isEmpty) xs_ else init subst st
        val st_ = assign(st, xs_, init_)

        val phi = wp(how, rest_, cont, scope, st_, old, live, not_live, post, brk, ret)
        Forall(xs_, phi)

      case Assign(xs, rhs) :: rest =>
        val rhs_ = rhs subst st // don't use eval, old is specification-only
        val st_ = assign(st, xs, rhs_)
        wp(how, rest, cont, scope, st_, old, live, not_live, post, brk, ret)

      // purely assert
      // case Spec(Nil, phi, True) :: rest =>
      //   val phi_ = eval(phi, scope, st, old)
      //   val chi = wp(how, rest, cont, scope, st, old, live, not_live, post, brk, ret)
      //   println("XXX: overriding assert with true")
      //   /* phi_ && */ chi

      case Spec(xs, phi, psi) :: rest =>
        val (xs_, re) = havoc(xs)
        val st_ = assign(st, xs, xs_)

        val phi_ = eval(phi, scope, st, old) source "assert"
        val psi_ = eval(psi, scope, st_, st :: old)
        val chi = wp(how, rest, cont, scope, st_, old, live, not_live, post, brk, ret)

        phi_ && how.spec(xs_, psi_, chi)

      case Call(name, in, out) :: rest =>
        require(state.procs contains name, "unknown procedure: " + name)

        val Proc(_, params, xs, zs, spec) = state procs name

        spec match {
          case None | Some(Spec(_, True, True)) if state.procdefs contains name =>
            // intentionally mirrors variables xs, ys, as procdef may refer to different vars than procdecl
            val block = Inline.inline(state, name, in, out)

            def cont_(st2: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) = {
              wp(how, rest, cont, scope, st2, old, live, not_live, post, brk, ret)
            }

            // inlined code should not have top-level breaks,
            // and should continue with rest program upon returns
            wp(how, List(block), Nil, scope, st, old, live, not_live, cont_, no_brk, cont_)

          case None =>
            cuvee.error(
              "inlining procedures not implemented, consider adding a contract to: " + name
            )

          case Some(Spec(mod, phi, psi)) =>
            val su = Expr.subst(xs, in)
            val re = Expr.subst(zs, out)
            val spec_ = Spec(mod ++ out, phi subst su, psi rename re subst su)
            wp(how, spec_ :: rest, cont, scope, st, old, live, not_live, post, brk, ret)
        }

      case If(test, left, right) :: rest =>
        val test_ = test subst st
        val left_ =
          wp(how, List(left), rest :: cont, scope, st, old, live, not_live, post, brk, ret)
        val right_ =
          wp(how, List(right), rest :: cont, scope, st, old, live, not_live, post, brk, ret)

        how split (test_, left_, right_)

      case While(test, body, term, inv_, sum_, frames) :: rest =>
        require(
          how != Dia,
          "while within diamond: reachability not implemented"
        )

        // variables modified by the loop
        val xm = body.mod
        val xs0 = xm.toList
        val (xs1, re) = havoc(xs0)

        val free = inv_ match {
          case Note(inv_, _, attrs) if attrs.contains("free") =>
            inv_
          case _ =>
            True
        }

        var inv = inv_ match {
          case Note(inv_, _, attrs) if attrs.contains("free") =>
            True
          case _ =>
            inv_
        }

        var sum = sum_

        // Add requirement that decreases clause is non-negative to invariant
        // XXX: this may be too strict, when we jump below zero but the test becomes false
        // if (how == WP)
        //   inv = inv && (Zero <= term)

        // Prepare some states:
        // 0. current state at loop entry
        // 1. arbitrary state at loop head before some iteration
        val st0 = st
        val st1 = assign(st, xs0, xs1)

        // invariant to show at loop head upon entry
        val inv0 = eval(inv, scope, st0, st0 :: old) source "invariant entry"

        // test and invariant at loop head before some iteration
        val test1 = test subst st1
        val inv1 = eval(inv && free, scope, st1, st0 :: old)

        // below we adjust the three exit cases (termination, break, return)
        // for a single iteration of the loop body

        def post_(st2: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) = {
          // invariant that needs to be preserved (from inv1)
          val inv2 = eval(inv, scope, st2, st0 :: old) source "invariant forward"

          // propagate summary from st2 to st1 wrt. arbitrary state stk
          val (xsk, re) = havoc(xs0)
          val stk = assign(st2, xs0, xsk)

          val sum1k = eval(sum, scope, stk, st1 :: old) source "summary backward"
          val sum2k = eval(sum, scope, stk, st2 :: old)

          val needs_decreases =
            how != Box || live.nonEmpty || not_live.nonEmpty

          // possibly add termination condition
          val term2 = if (needs_decreases) {
            val test2 = test subst st2
            val term1 = eval(term, scope, st1, st0 :: old)
            val term2 = eval(term, scope, st2, st0 :: old)

            // Note: can assume test is positive otherwise loop terminates anyway
            test2 ==> (Zero <= term2 && term2 < term1) source "decreases"
          } else {
            True
          }

          // ensure this formula after a regular loop termination
          inv2 && term2 && Forall(xsk, sum2k ==> sum1k)
        }

        def brk_(st2: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) = {
          // establish summary for last partial iteration
          val sum12 = eval(sum, scope, st2, st1 :: old)

          // how we continue after the loop, assuming the summary of the entire loop
          val sum02 = eval(sum, scope, st2, st0 :: old)
          val exit2 = wp(how, rest, cont, scope, st2, old, live, not_live, post, brk, ret)

          // ensure this formula after a break
          (sum12 ==> sum02) ==> exit2
        }

        def ret_(st2: Map[Var, Expr], live: Set[Id], not_live: Set[Id]) = {
          // analogously to break we extend the partial summary to a complete one
          val sum02 = eval(sum, scope, st2, st0 :: old)
          val sum12 = eval(sum, scope, st2, st1 :: old)

          // ensure whatever postcondition we had previously on return
          (sum12 ==> sum02) ==> ret(st2, live, not_live)
        }

        // below, we define the base case and the step case
        // in relation to whether the test evaluates to true

        val base1 = {
          // establish summary reflexively
          val sum11 = eval(sum, scope, st1, st1 :: old)

          // how we continue after the loop, assuming the summary of the entire loop
          val sum01 = eval(sum, scope, st1, st0 :: old)
          val exit1 = wp(how, rest, cont, scope, st1, old, live, not_live, post, brk, ret)

          // ensure this formula at regular loop exit
          sum11 && (sum01 ==> exit1)
        }

        val step1 = {
          // run the loop body, establishing the post/break/return conditions defined above
          wp(how, List(body), Nil, scope, st1, st0 :: old, live, not_live, post_, brk_, ret_)
        }

        // ensure invariant now and base/step case at an arbitrary iteration
        inv0 && Forall(xs1, inv1 ==> how.split(test1, step1, base1))
    }
}

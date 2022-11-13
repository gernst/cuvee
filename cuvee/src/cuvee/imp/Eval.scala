package cuvee.imp

import cuvee.error
import cuvee.pure._
import cuvee.State

object Eval {
  var infer: Set[String] = Set()
}

class Eval(state: State) {
  import Eval.infer

  def eval(
      expr: Expr,
      scope: Map[Var, Expr],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]]
  ): Expr =
    expr match {
      case x: Var if (st contains x) =>
        st(x)

      case x: Var if (scope contains x) =>
        scope(x)

      case x: Var =>
        error("undefined program variable: " + x + " in state " + st.keys.mkString(" ") + " and scope " + scope.keys.mkString(" "))

      case _: Lit =>
        expr

      case Old(expr) =>
        require(
          old.nonEmpty,
          "cannot evaluate old expression, no previous state(s) given"
        )
        eval(expr, scope, old.head, old.tail)

      case App(inst, args) =>
        val args_ = args map (eval(_, scope, st, old))
        App(inst, args_)

      case bind @ Bind(quant, xs, body, typ) =>
        val re = bind.avoid(Expr.free(st))
        val su = Expr.subst(xs map {
          case x if re contains x => (x, re(x))
          case x                  => (x, x)
        })

        val xs_ = xs rename re
        val body_ = eval(body, scope ++ su, st, old)
        Bind(quant, xs_, body_, typ)
    }

  def havoc(xs: List[Var]) = {
    val re = Expr.fresh(xs)
    val xs_ = xs rename re
    (xs_, re)
  }

  def assign(st: Map[Var, Expr], xs: List[Var], es: List[Expr]) = {
    st ++ (xs zip es)
  }

  type Exit = Map[Var, Expr] => Expr

  def no_brk(st: Any) =
    cuvee.error("break not within while loop")

  def no_ret(st: Any) =
    cuvee.error("return not within procedure")

  def wp(
      how: Modality,
      prog: Prog,
      st: Map[Var, Expr],
      post: Expr,
      old: List[Map[Var, Expr]] = Nil
  ): Expr = {
    wp(
      how,
      List(prog),
      Nil,
      Map(),
      st,
      old,
      eval(post, Map(), _, old),
      no_brk,
      no_ret
    )
  }

  def wp_proc(
      how: Modality,
      prog: Prog,
      st: Map[Var, Expr],
      post: Expr
  ): Expr = {
    val old = List(st)

    wp(
      how,
      List(prog),
      Nil,
      Map(),
      st,
      old,
      eval(post, Map(), _, old),
      no_brk,
      eval(post, Map(), _, old)
    )
  }

  def wp(
      how: Modality,
      progs: List[Prog], /* current block */
      cont: List[List[Prog]],
      scope: Map[Var, Expr],
      st: Map[Var, Expr],
      old: List[Map[Var, Expr]],
      post: Exit,
      brk: Exit,
      ret: Exit
  ): Expr =
    progs match {
      case Nil =>
        cont match {
          case Nil =>
            post(st)
          case progs :: cont =>
            // Note: no need to cleanup locals from st,
            //       we rename them when we introduce them
            wp(how, progs, cont, scope, st, old, post, brk, ret)
        }

      case Block(progs) :: rest =>
        wp(how, progs, rest :: cont, scope, st, old, post, brk, ret)

      case Break :: rest =>
        brk(st)

      case Return :: rest =>
        ret(st)

      case Local(xs, init) :: rest =>
        // Note: ensure we introduce fresh names for the locals
        //       and compute on these within the current block (but not in cont)
        val (ys, zs) = xs partition st.contains
        val (ys_, re) = havoc(ys)
        val xs_ = ys_ ++ zs
        val rest_ = rest replace re
        val init_ = if (init.isEmpty) xs_ else init subst st
        val st_ = assign(st, xs_, init_)

        val phi = wp(how, rest_, cont, scope, st_, old, post, brk, ret)
        Forall(xs_, phi)

      case Assign(xs, rhs) :: rest =>
        val rhs_ = rhs subst st // don't use eval, old is specification-only
        val st_ = assign(st, xs, rhs_)
        wp(how, rest, cont, scope, st_, old, post, brk, ret)

      case Spec(xs, phi, psi) :: rest =>
        val (xs_, re) = havoc(xs)
        val st_ = assign(st, xs, xs_)

        val phi_ = eval(phi, scope, st, old)
        val psi_ = eval(psi, scope, st_, st :: old)
        val chi = wp(how, rest, cont, scope, st_, old, post, brk, ret)

        phi_ && how.spec(xs_, psi_, chi)

      case Call(name, in, out) :: rest =>
        require(state.procs contains name, "unknown procedure: " + name)

        val Proc(_, params, xs, zs, spec) = state procs name

        spec match {
          case None =>
            cuvee.error("inlining procedures not implemented, consider adding a contract to: " + name)

          case Some(Spec(mod, phi, psi)) =>
            val su = Expr.subst(xs, in)
            val re = Expr.subst(zs, out)
            val spec_ = Spec(mod, phi subst su, psi subst (su ++ re))
            wp(how, spec_ :: rest, cont, scope, st, old, post, brk, ret)
        }

      case If(test, left, right) :: rest =>
        val test_ = test subst st
        val left_ =
          wp(how, List(left), rest :: cont, scope, st, old, post, brk, ret)
        val right_ =
          wp(how, List(right), rest :: cont, scope, st, old, post, brk, ret)

        how split (test_, left_, right_)

      case While(test, body, term, inv, sum_, frames) :: rest =>
        require(
          how != Dia,
          "while within diamond: reachability not implemented"
        )

        // variables modified by the loop
        val xm = body.mod
        val xs0 = xm.toList
        val (xs1, re) = havoc(xs0)

        var sum = sum_

        // Prepare some states:
        // 0. current state at loop entry
        // 1. arbitrary state at loop head before some iteration
        val st0 = st
        val st1 = assign(st, xs0, xs1)
        
        // invariant to show at loop head upon entry
        val inv0 = eval(inv, scope, st0, st0 :: old)

        // test and invariant at loop head before some iteration
        val test1 = test subst st1
        val inv1 = eval(inv, scope, st1, st0 :: old)

        // below we adjust the three exit cases (termination, break, return)
        // for a single iteration of the loop body

        def post_(st2: Map[Var, Expr]) = {
          // invariant that needs to be preserved (from inv1)
          val inv2 = eval(inv, scope, st2, st0 :: old)

          // propagate summary from st2 to st1 wrt. arbitrary state stk
          val (xsk, re) = havoc(xs0)
          val stk = assign(st2, xs0, xsk)

          val sum1k = eval(sum, scope, stk, st1 :: old)
          val sum2k = eval(sum, scope, stk, st2 :: old)

          // possibly add termination condition
          val term2 = if (how == WP) {
            val test2 = test subst st2
            val term1 = eval(term, scope, st1, st0 :: old)
            val term2 = eval(term, scope, st2, st0 :: old)

            // Note: can assume test is positive otherwise loop terminates anyway
            test2 ==> (Zero <= term2 && term2 < term1)
          } else {
            True
          }

          // ensure this formula after a regular loop termination
          inv2 && term2 && Forall(xsk, sum2k ==> sum1k)
        }

        def brk_(st2: Map[Var, Expr]) = {
          // establish summary for last partial iteration
          val sum12 = eval(sum, scope, st2, st1 :: old)

          // how we continue after the loop, assuming the summary of the entire loop
          val sum02 = eval(sum, scope, st2, st0 :: old)
          val exit2 = wp(how, rest, cont, scope, st2, old, post, brk, ret)

          // ensure this formula after a break
          (sum12 ==> sum02) ==> exit2
        }

        def ret_(st2: Map[Var, Expr]) = {
          // analogously to break we extend the partial summary to a complete one
          val sum02 = eval(sum, scope, st2, st0 :: old)
          val sum12 = eval(sum, scope, st2, st1 :: old)

          // ensure whatever postcondition we had previously on return
          (sum12 ==> sum02) ==> ret(st2)
        }

        // below, we define the base case and the step case
        // in relation to whether the test evaluates to true

        val base1 = {
          // establish summary reflexively
          val sum11 = eval(sum, scope, st1, st1 :: old)

          // how we continue after the loop, assuming the summary of the entire loop
          val sum01 = eval(sum, scope, st1, st0 :: old)
          val exit1 = wp(how, rest, cont, scope, st1, old, post, brk, ret)

          // ensure this formula at regular loop exit
          sum11 && (sum01 ==> exit1)
        }

        val step1 = {
          // run the loop body, establishing the post/break/return conditions defined above
          wp(how, List(body), Nil, scope, st1, st0 :: old, post_, brk_, ret_)
        }

        // ensure invariant now and base/step case at an arbitrary iteration
        inv0 && Forall(xs1, inv1 ==> how.split(test1, step1, base1))
    }
}

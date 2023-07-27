package cuvee.imp

import cuvee.pure._

sealed trait Conf

/* Note: all path formulas and phi are already evaluated */
case class Asserted(fresh: List[Var], path: List[Expr], phi: Expr) extends Conf
case class Returned(fresh: List[Var], path: List[Expr], subst: Map[Var, Expr]) extends Conf
case class Breaked(fresh: List[Var], path: List[Expr], subst: Map[Var, Expr]) extends Conf
case class Stopped(fresh: List[Var], path: List[Expr], subst: Map[Var, Expr]) extends Conf

class Exec(evals: Eval) {
  import evals.state
  import evals.havoc
  import evals.assign
  import evals.eval

  def exec(
      prog: Prog, // current block, affected by local variables
      cont: List[List[Prog]], // anything after the current block
      fresh: List[Var], // any new variables introduced
      path: List[Expr], // current path condition
      scope: Map[Var, Expr], // assignment of logical variables (why needed?)
      st: Map[Var, Expr], // all program variables
      old: List[Map[Var, Expr]]
  ): List[Conf] = {
    exec(List(prog), cont, fresh, path, scope, st, old)
  }

  def exec(
      progs: List[Prog], // current block, affected by local variables
      cont: List[List[Prog]], // anything after the current block
      fresh: List[Var], // any new variables introduced
      path: List[Expr], // current path condition
      scope: Map[Var, Expr], // assignment of logical variables (why needed?)
      st: Map[Var, Expr], // all program variables
      old: List[Map[Var, Expr]]
  ): List[Conf] = {
    progs match {
      case Nil =>
        cont match {
          case Nil =>
            List(Stopped(fresh, path, st))

          case progs :: cont =>
            exec(progs, cont, fresh, path, scope, st, old)
        }

      case Block(progs) :: rest =>
        exec(progs, rest :: cont, fresh, path, scope, st, old)

      case Return :: rest =>
        List(Returned(fresh, path, st))

      case Break :: rest =>
        List(Breaked(fresh, path, st))

      case Local(xs, init) :: rest =>
        // Note: ensure we introduce fresh names for the locals
        //       and compute on these within the current block (but not in cont)
        val (ys, zs) = xs partition st.contains
        val (ys_, re) = havoc(ys)
        val xs_ = ys_ ++ zs
        val fresh_ = fresh ++ xs_
        val rest_ = rest replace re
        val init_ = if (init.isEmpty) xs_ else init subst st
        val st_ = assign(st, xs_, init_)

        exec(rest_, cont, fresh_, path, scope, st_, old)

      case Assign(xs, rhs) :: rest =>
        val rhs_ = rhs subst st // don't use eval, old is specification-only
        val st_ = assign(st, xs, rhs_)
        exec(rest, cont, fresh, path, scope, st_, old)

      case Spec(xs, phi, psi) :: rest =>
        val (xs_, re) = havoc(xs)
        val fresh_ = fresh ++ xs_
        val st_ = assign(st, xs, xs_)
        val phi_ = eval(phi, scope, st, old)
        val psi_ = eval(psi, scope, st_, st :: old)

        val first_ = Asserted(fresh_, path, phi_)
        val rest_ = exec(rest, cont, fresh_, path ++ List(psi_), scope, st_, old)
        first_ :: rest_

      case Call(name, in, out) :: rest =>
        require(state.procs contains name, "unknown procedure: " + name)
        val Proc(_, params, xs, zs, spec) = state procs name

        spec match {
          case None =>
            cuvee.error(
              "inlining procedures not implemented, consider adding a contract to: " + name
            )

          case Some(Spec(mod, phi, psi)) =>
            val su = Expr.subst(xs, in)
            val re = Expr.subst(zs, out)
            val spec_ = Spec(mod, phi subst su, psi subst (su ++ re))
            exec(spec_ :: rest, cont, fresh, path, scope, st, old)
        }

      case If(test, left, right) :: rest =>
        val test_ = test subst st
        val left_ = exec(left, cont, fresh, path ++ List(test_), scope, st, old)
        val right_ = exec(right, cont, fresh, path ++ List(!test_), scope, st, old)
        left_ ++ right_

      case While(test, body, term, inv, sum, frames) :: rest =>
        // variables modified by the loop
        val xm = body.mod
        val xs0 = xm.toList
        val (xs1, re) = havoc(xs0)

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

        ???
    }
  }
}

package cuvee.imp

import cuvee.pure._
import cuvee.smtlib._
import cuvee.pipe.Stage
import scala.collection.immutable

object Annotate extends Stage {
  case class State(path: List[Expr], vars: Map[Var, Expr])

  def exec(prefix: List[Cmd], cmds: List[Cmd], state: cuvee.State) = {
    cmds flatMap {
      case DefineProc(name, params, in, out, spec, body) =>
        val proc = Proc(name, params, in, out, spec)
        val body_ = annotate(proc, body)
        List(DefineProc(name, params, in, out, spec, body_))

      case cmd =>
        List(cmd)
    }
  }

  def assume(from: List[State], phi: Expr) = {
    for (State(path, vars) <- from)
      yield State((phi subst vars) :: path, vars)
  }

  // def spec(from: List[State], xs: List[Var], phi: Expr, psi: Expr) = {
  //   for (State(path, vars) <- from)
  //     yield {
  //       val re = Expr.fresh(xs)

  //       State((phi subst vars) :: path, vars)
  //     }
  // }

  def assign(from: List[State], xs: List[Var], rhs: List[Expr]) = {
    for (State(path, vars) <- from)
      yield State(path, vars ++ (xs zip (rhs map (_ subst vars))))
  }

  def havoc(from: List[State], xs: Set[Var]) = {
    // renaming of existing occurrences to new variables
    val re = Expr.fresh(xs)
    val xs_ = xs.toList rename re

    // reset variables to some current values
    val id = Expr.id(xs)

    for (State(path, vars) <- from)
      yield {
        val vars_ = Expr.compose(vars, re)
        val (keep, zap) = path partition (_.free disjoint xs)

        val phi = Exists(xs_, And(zap subst vars_))
        State(phi :: keep, vars ++ id)
      }
  }

  def annotate(
      proc: Proc,
      body: Prog
  ): Prog = proc match {
    case Proc(name, params, in, out, None) =>
      val vars = Expr.id(in ++ out)
      val from = State(Nil, vars)
      val (prog, _) = annotate(List(from), body)
      prog

    case Proc(name, params, in, out, Some(Spec(gobals, pre, post))) =>
      val vars = Expr.id(in ++ out)
      val from = State(And.flatten(pre), vars)
      val (prog, _) = annotate(List(from), body)
      prog
  }

  def annotate(
      from: List[State],
      progs: List[Prog]
  ): (List[Prog], List[State]) = progs match {
    case Nil =>
      (Nil, from)

    case prog :: rest =>
      val (prog_, via) = annotate(from, prog)
      val (rest_, to) = annotate(via, rest)
      (prog_ :: rest_, to)
  }

  def annotate(
      from: List[State],
      prog: Prog
  ): (Prog, List[State]) = {
    prog match {
      case Block(progs) =>
        val (progs_, to) = annotate(from, progs)
        (Block(progs_), to)

      case Return =>
        (Return, Nil)

      case Break =>
        (Break, Nil)

      case first @ Local(xs, init) =>
        val all = from flatMap (_.vars.keys)
        val bad = xs.toSet & all.toSet
        require(init.nonEmpty, "local variables must be initialized: " + xs)
        require(bad.isEmpty, "local variables " + bad + " already exist")
        (first, assign(from, xs, init))

      case first @ Assign(xs, rhs) =>
        (first, assign(from, xs, rhs))

      case (first @ Spec(xs, phi, psi)) =>
        cuvee.error(
          "assume/assert currently not supported during annotation generation"
        )

      //   val (xs_, re) = havoc(xs)
      //   val st_ = assign(st, xs, xs_)
      //   // val phi_ = eval(phi, scope, st, old)
      //   val psi_ = eval(psi, scope, st_, st :: old)

      //   (first, List(Stopped(fresh, path ++ List(psi_), st_)))

      case Call(name, in, out) =>
        cuvee.error(
          "calls currently not supported during annotation generation"
        )
      //   require(state.procs contains name, "unknown procedure: " + name)
      //   val Proc(_, params, xs, zs, spec) = state procs name

      //   spec match {
      //     case None =>
      //       cuvee.error(
      //         "inlining procedures not implemented, consider adding a contract to: " + name
      //       )

      //     case Some(Spec(mod, phi, psi)) =>
      //       val su = Expr.subst(xs, in)
      //       val re = Expr.subst(zs, out)
      //       val spec_ = Spec(mod, phi subst su, psi subst (su ++ re))
      //       annotate(spec_, fresh, path, scope, st, old)
      //   }

      case If(test, left, right) =>
        val (left_, to1) = annotate(assume(from, test), left)
        val (right_, to2) = annotate(assume(from, !test), right)
        (If(test, left_, right_), to1 ++ to2)

      case While(test, body, term, inv, sum, frames) =>
        val mod = body.mod
        val via = havoc(from, mod)

        val before = assume(via, inv && test)
        val (body_, after) = annotate(before, body)

        // HERE: after are all states reachable from before,
        //       such that before -- body -> after is exactly one arbitrary loop iteration

        // TODO: compute some new invariants here

        // Arbitrary integer variable to reason about all of them
        val x = Var("x", Sort.int)

        def isModifiedArray(a: Var) = a.typ match {
          case Sort(Con.array, _) if mod.contains(a) => true
          case _                                     => false
        }

        /** Provides an expression, which describes an assignment to an array
          *
          * @param lhs
          *   left hand side of the assignment, the array to write to
          * @param a
          *   array from which to take the values
          * @param idx
          *   index from a to read from
          * @param rhs
          *   right hand side of the assignment, the value to write into lhs
          * @param fresh
          *   rename variables to given fresh ones if needed
          * @param subst
          *   rename variables to some integer if not to fresh
          * @return
          */
        def modified(
            lhs: Var,
            a: Expr,
            idx: Expr,
            rhs: Expr,
            fresh: Map[Var, Var],
            subst: Map[Var, Var]
        ): Expr = a match {
          case Var(name, typ) if lhs == a && rhs.isInstanceOf[Var] =>
            Select(a, x) === rhs rename fresh
          case Var(name, typ) if lhs == a =>
            Select(a, idx) === rhs rename subst
          case Var(name, typ) =>
            lhs === Store(a, idx, rhs) rename subst
          case Store(a_, idx_, _) if idx == idx_ =>
            modified(lhs, a_, idx, rhs, fresh, subst)
          case Store(a_, idx_, rhs_) =>
            modified(lhs, a_, idx, rhs, fresh, subst) &&
            modified(lhs, a_, idx_, rhs_, fresh, subst)
          case _ =>
            cuvee.error("Unexpected case in " + this)
        }

        /** Gives the value with which x was initialized
          *
          * @param x
          *   variable to get the initial value for
          * @return
          *   initial value of x
          */
        def init(x: Var) = {
          // initial
          val xs = from map { st => st.vars(x) }
          // try to get the single value for i0, just fail otherwise
          val List(x_) = xs.distinct
          x_
        }

        /** Builds an instance of Modified which holds the range of indices
          * which got edited until an arbitrary iteration of the analyzed loop
          *
          * @param expr
          *   position of an assignment to derive Modified for
          * @return
          *   Modified which got derived from the given Expr
          */
        def mOf(expr: Expr): Modified = expr match {
          case x @ Var(_, Sort.int) =>
            val x0 = init(x)
            // TODO this may not hold -> it is not given to go from left to right

            val stepxs = after map { st => st.vars(x) }
            val List(step) = stepxs.distinct

            Modified(x0, x, step)
          case c @ Lit(_, Sort.int) =>
            Modified(c, c)
          case Plus(args) =>
            val ranges = args map mOf
            ranges.reduce((x, y) =>
              Modified(x.lb + y.lb, x.ub + y.ub, x.step + y.step)
            )
          case Minus(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            ranges.reduce((x, y) =>
              Modified(x.lb - y.lb, x.ub - y.ub, x.step + y.step)
            )
          case Times(args) =>
            val ranges = args map mOf
            ranges.reduce((x, y) =>
              Modified(x.lb * y.lb, x.ub * y.ub, x.step + y.step)
            )
          case DivBy(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            ranges.reduce((x, y) =>
              Modified(DivBy(x.lb, y.lb), DivBy(x.ub, y.ub), x.step + y.step)
            )
          case Mod(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            ranges.reduce((x, y) =>
              Modified(Mod(x.lb, y.lb), Mod(x.ub, y.ub), x.step + y.step)
            )
          case UMinus(args) =>
            val ranges = List(mOf(args))
            // TODO is this even possible? If it is: How?
            ranges.reduce((x, y) =>
              Modified(
                UMinus(x.lb + y.lb),
                UMinus(x.ub + y.ub),
                x.step + y.step
              )
            )
          case _ =>
            cuvee.error("Could not construct Modified from Expr: " + expr)
        }

        /** Generates a new variable for each element in xs
          *
          * @param xs
          *   List of variables
          * @return
          *   Map variable -> fresh variable
          */
        def fresh(xs: List[Var]) = {
          val re = Expr.fresh(xs)
          val xs_ = xs rename re
          (xs_, re)
        }

        /** Substitutes a given List of variables with one given variable
          *
          * @param xs
          *   list of Var to be replaced
          * @param v
          *   Var to map elements from xs to
          * @return
          *   Map from elements of xs to v
          */
        def subst(xs: List[Var], v: Var) = {
          val subst_ = for (e <- xs) yield e -> v
          subst_.toMap
        }

        /* Try to derive an invariant for a given while loop possibly
         * containing assignments to array.
         *
         * In case of an assignment to an array the utilized approach consists
         * of the collection of all modified indices and an observation, in
         * which way an array got modified.
         */
        val derive = for (st1 <- before; st2 <- after) yield {
          // TODO
          val path = And(st1.path)

          val all =
            for ((array, assign) <- st2.vars if isModifiedArray(array)) yield {
              assign match {
                case Store(a, idx, rhs) =>
                  val m = mOf(idx)
                  // Only variables who change in the loop need substitutes
                  val modifiedVars = m.vars.intersect(mod).toList
                  val (freshVars, freshMapping) = fresh(modifiedVars)
                  val subst_ = subst(modifiedVars, x)

                  // Expression which describes all modified indices
                  // val prem = m.toExpr(x)
                  val prem = init(
                    modifiedVars.head
                  ) <= (m.ub rename subst_) && (m.ub rename subst_) < modifiedVars.head
                  // TODO with this array_init_both_end_multible_sum as well as copy work. figure out, what you actually need

                  /* DO NOT WORK:
                    examples/boogie/modified/array_tiling_tcpy.bpl
                    examples/boogie/modified/array_tripl_access_init_const.bpl
                    examples/boogie/modified/index_plus_one.bpl
                    examples/boogie/modified/multible_vars.bpl
                   */

                  // Multible assigns in one iteration (at different indices)
                  // need modified -> adapt it

                  // TODO ROADMAP
                  // 1 Boundings
                  //    - One M pro assign-idx -> OR(M)
                  //    - Boundings -> What is inclusive, what exclusive?

                  // How and at which indices got the array in question modified
                  val where = x === (idx rename freshMapping)
                  val how = modified(array, a, idx, rhs, freshMapping, subst_)
                  val mod_ = Exists(freshVars, where && how)

                  // Every index which got not visited should not be modified
                  val notMod = Select(array, x) === Old(Select(array, x))

                  (prem ==> mod_) && (!prem ==> notMod)
                case _ =>
                  cuvee.error(
                    "Here only modified arrays should be handled. Got: " + (array, assign)
                  )
              }
            }
          // TODO ask regarding path
          Forall(List(x), And(all.toList))
        }

        val inv_ = inv && And(derive)

        val prog_ = While(test, body_, term, inv_, sum, frames)

        // prepare states after the loop
        val to = assume(via, inv_ && !test)

        (prog_, to)
    }
  }
}

/** Class to keep track of modified indices for one array
  *
  * @param lb
  *   lower bound of the modified range
  * @param ub
  *   upper bound of the modified range
  * @param step
  *   in which the indices change e.g. One for i := i + 1 and Two for i := i + 2
  *   Can also hold more complicated calculations. However: The expression are *
  *   held as is and will not be simplified
  */
sealed case class Modified(lb: Expr, ub: Expr, step: Expr = One) {

  /** Provides an expression describing all indices which got changed to place
    * into an invariant
    *
    * @param x
    *   an arbitrary integer to reason about the boundings in this instance
    * @return
    *   one expression containing all necessary informations which indices got
    *   changed
    */
  // TODO add step
  def toExpr(x: Var): Expr = this.lb <= x && x < this.ub

  /** Find all variables that are part of the expressions
    *
    * @return
    *   List of all variables who are part of the expressions from this instance
    */
  def vars(): Set[Var] = {
    ub match {
      case Var(name, typ)  => Set(Var(name, typ))
      case App(inst, args) => vars(args).toSet
      case _               => Set()
    }
  }

  private[this] def vars(args: List[Expr]): List[Var] = args match {
    case Var(name, typ) :: next => Var(name, typ) :: vars(next)
    case App(_, args_) :: next  => vars(args_) ++ vars(next)
    case head :: next           => vars(next)
    case Nil                    => Nil
  }
}

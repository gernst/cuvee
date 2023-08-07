package cuvee.imp

import cuvee.pure._
import cuvee.smtlib._
import cuvee.pipe.Stage

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

        val x = Var("x", Sort.int)
        val x_ = List(x)

        // TODO
        val M = Var("M_", Sort.array(Sort.int, Sort.bool))
        val i_ = Var("i_", Sort.int)

        // TODO init M with false -> assume in body
        // get all idx from lhs + place in M
        // inv for M
        // add M to body

        def isModifiedArray(a: Var) = a.typ match {
          case Sort(Con.array, _) if mod.contains(a) => true
          case _                                     => false
        }

        def toM(idx: Expr) = Store(M, idx, True)

        val which = for (st1 <- before; st2 <- after) yield {
          val modified =
            for ((var_, expr_) <- st2.vars if isModifiedArray(var_)) yield {
              expr_ match {
                // TODO buld one M for all integer variables with increments in body
                // TODO store correct idx in fitting M
                case Store(a, idx, rhs) if var_ == a => toM(idx)
                case Store(a, idx, rhs)              => toM(idx)
              }
            }

          // TODO current range e.g. 0 <= i_ && i_ < idx
          var idx = for ((var_, expr_) <- st2.vars) yield {
            Var("TODO", Sort.int)
          }
          var init = Var("initTODO", Sort.int)

          val prelude = Select(M, x)
          val fine = Exists(List(i_), i_ === x && init <= i_ && i_ <= idx.head)

          prelude === fine
        }

        def modified(lhs: Var, a: Expr, idx: Expr, rhs: Expr): Expr = a match {
          case Var(name, typ) if lhs == a =>
            Select(a, idx) === rhs
          case Var(name, typ) =>
            lhs === Store(a, idx, rhs)
          case Store(a_, idx_, _) if idx == idx_ =>
            modified(lhs, a_, idx, rhs)
          case Store(a_, idx_, rhs_) =>
            modified(lhs, a_, idx, rhs) && modified(lhs, a_, idx_, rhs_)
        }

        // TODO better design
        def mOf(expr: Expr): List[Modified] = expr match {
          case x @ Var(_, Sort.int) =>
            // initial
            val xs0 = from map { st => st.vars(x) }
            // try to get the single value for i0, just fail otherwise
            val List(x0) = xs0.distinct

            // TODO cover multible assigns, possibly empty
            val stepx = after map { st => st.vars(x) }
            val List(step_) = stepx.distinct

            // TODO get int from expr
            val step = 1

            List(Modified(x0, x, step))
          case c @ Lit(_, Sort.int) =>
            List(Modified(c, c))
          case Plus(args) =>
            val ranges = args map mOf
            // TODO take op into account
            ranges.flatten
          case Minus(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            // TODO take op into account
            ranges.flatten
          case Times(args) =>
            val ranges = args map mOf
            // TODO take op into account
            ranges.flatten
          case DivBy(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            // TODO take op into account
            ranges.flatten
          case Mod(args) =>
            val (l, r) = args
            val ranges = List(mOf(l), mOf(r))
            // TODO take op into account
            ranges.flatten
          case UMinus(args) =>
            val ranges = List(mOf(args))
            // TODO take op into account
            ranges.flatten
          case _ =>
            cuvee.error(
              String.format("Could not construct Modified from Expr %s.", expr)
            )
        }

        val how = for (st1 <- before; st2 <- after) yield {
          val path = And(st1.path)

          val all =
            for ((var_, expr_) <- st2.vars if isModifiedArray(var_)) yield {
              expr_ match {
                case Store(a, idx, rhs) =>
                  // TODO get var from idx expr for M and re
                  println(idx)

                  println()

                  println(mOf(idx))

                  println()

                  // TODO construct M from List provided by mOf
                  val prem = Select(M, x)

                  val re = Expr.subst(Var(idx.toString, idx.typ) -> x)
                  val mod = modified(var_, a, idx, rhs) rename re

                  val notMod = Select(var_, x) === Old(Select(var_, x))

                  prem ==> mod && !prem ==> notMod
              }
            }

          path && Forall(x_, And(all.toList))
        }

        // TODO: the same for all integer variables that are modified
        val i = Var("i", Sort.int)

        // initial
        val is0 = from map { st => st.vars(i) }
        // try to get the single value for i0, just fail otherwise
        val List(i0) = is0.distinct

        // after an arbitrary iteration
        val is_ = after map { st => st.vars(i) }
        val isIncremented = is_.forall {
          case Succ(`i`)         => true
          case Succ(j) if i == j => true // same as line above
          case _                 => false
        }

        val inv_ = inv && And(which) && And(how)

        val prog_ = While(test, body_, term, inv_, sum, frames)

        // prepare states after the loop
        val to = assume(via, inv_ && !test)

        (prog_, to)
    }
  }
}

sealed case class Modified(lb: Expr, ub: Expr, step: Int = 1)

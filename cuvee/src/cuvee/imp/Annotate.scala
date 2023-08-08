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

        val x = Var("x", Sort.int)

        // TODO
        // init M with false -> assume in body
        // get all idx from lhs + place in M
        // add M to body

        def isModifiedArray(a: Var) = a.typ match {
          case Sort(Con.array, _) if mod.contains(a) => true
          case _                                     => false
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
          case _ =>
            cuvee.error("Unexpected case in " + this)
        }

        def init(x: Var) = {
          // initial
          val xs = from map { st => st.vars(x) }
          // try to get the single value for i0, just fail otherwise
          val List(x_) = xs.distinct
          x_
        }

        // TODO to many Zero
        def getStep(exprs: List[Expr], v: Var): Expr = exprs match {
          case Var(name, typ) :: next if Var(name, typ) != v =>
            Plus(Var(name, typ), getStep(next, v))
          case App(inst, args) :: next =>
            Plus(getStep(args, v), getStep(next, v))
          case Lit(any, typ) :: next =>
            Plus(Lit(any, typ), getStep(next, v))
          case head :: next =>
            getStep(next, v)
          case Nil =>
            Zero
        }

        // TODO better design
        def mOf(expr: Expr): Modified = expr match {
          case x @ Var(_, Sort.int) =>
            val x0 = init(x)

            val stepx = after map { st => st.vars(x) }

            val step = getStep(stepx, x)
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
            cuvee.error(
              String.format("Could not construct Modified from Expr %s.", expr)
            )
        }

        def subst(xs: List[Var]) = {
          val re = Expr.fresh(xs)
          val xs_ = xs rename re
          (xs_, re)
        }

        val derive = for (st1 <- before; st2 <- after) yield {
          val path = And(st1.path)

          val all =
            for ((var_, expr_) <- st2.vars if isModifiedArray(var_)) yield {
              expr_ match {
                case Store(a, idx, rhs) =>
                  val m = mOf(idx)
                  val (substVars, substMapping) = subst(m.vars)

                  val prem = Select(m.toExpr(), x)
                  val pos = m.ub rename substMapping

                  val ixs = test match {
                    case App(inst, args) =>
                      for (arg <- args; i <- m.vars if arg == i) yield i
                    case _ => cuvee.error("Non App Expr in Test. " + test)
                  }
                  val List(i) = ixs.distinct
                  val i_ = i rename substMapping

                  val boundaries = x === pos && init(i) <= i_ && i_ <= i
                  val exists = Exists(substVars, boundaries)

                  val which = prem === exists

                  val mod = modified(var_, a, idx, rhs) rename substMapping
                  val notMod = Select(var_, x) === Old(Select(var_, x))
                  val how = prem ==> mod && !prem ==> notMod

                  which && how
              }
            }
          path && Forall(List(x), And(all.toList))
        }

        val inv_ = inv && And(derive)

        val prog_ = While(test, body_, term, inv_, sum, frames)

        // prepare states after the loop
        val to = assume(via, inv_ && !test)

        (prog_, to)
    }
  }
}

sealed case class Modified(lb: Expr, ub: Expr, step: Expr = One) {
  def name(): String = "M_" + ub
  // TODO how give ranges to array?
  def toExpr(): Expr = Var(name(), Sort.array(Sort.int, Sort.bool))

  def vars(): List[Var] = {
    ub match {
      case Var(name, typ)  => List(Var(name, typ))
      case App(inst, args) => vars(args)
      case _               => Nil
    }
  }

  def vars(args: List[Expr]): List[Var] = args match {
    case x @ Var(name, typ) :: next => Var(name, typ) :: vars(next)
    case a @ App(_, args_) :: next  => vars(args_) ++ vars(next)
    case head :: next               => vars(next)
    case Nil                        => Nil
  }
}

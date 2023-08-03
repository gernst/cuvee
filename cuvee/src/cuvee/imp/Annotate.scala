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
        val i_ = Var("i_", Sort.int)

        val M = Var("M", Sort.array(Sort.int, Sort.bool))
        // TODO init M with false

        // get all idx from lhs + place in M
        // inv for M
        // add M to body

        def isModifiedArray(a: Var) = a.typ match {
          case Sort(Con.array, args) if mod.contains(a) => true
          case _                                        => false
        }

        def toM(idx: Expr) = Store(M, idx, True)

        // TODO get counter from test
        def isCounter(i: Expr) = {
          println(test, test.typ)
          true
        }

        val which = for (st2 <- after) yield {
          val modified =
            for ((var_, expr_) <- st2.vars if isModifiedArray(var_)) yield {
              expr_ match {
                case Store(a, idx, rhs) => toM(idx)
              }
            }

          // TODO current range e.g. 0 <= i_ && i_ < idx
          // get var from test, search assign, use init of var as lb, var as is as ub
          var idx = for ((var_, expr_) <- st2.vars if isCounter(var_)) yield {
            Var("TODO", Sort.int)
          }
          var init = Var("initTODO", Sort.int)

          val prelude = Select(M, x)
          val fine = Exists(List(i_), i_ === x && init <= i_ && i_ <= idx.head)

          prelude === fine
        }

        def getRhs(rhs: Expr): Expr = rhs match {
          case Var(name, typ) => rhs
          case Lit(any, typ)  => rhs
          case Select(b, idx) => Select(Old(b), idx) // TODO: not correct, don't use old here
        }

        def modify(a: Expr, idx: Expr, rhs: Expr): Expr = a match {
          case Var(name, typ)                    => Select(a, idx) === rhs // getRhs(rhs)
          case Store(a_, idx_, _) if idx == idx_ => modify(a_, idx, rhs)
          case Store(a_, idx_, rhs_) =>
            modify(a_, idx, rhs) && modify(a_, idx_, rhs_)
        }

        val how = for (st1 <- before; st2 <- after) yield {
          val modified =
            for ((var_, expr_) <- st2.vars if isModifiedArray(var_)) yield {
              expr_ match {
                case Store(a, idx, rhs) => modify(a, idx, rhs)
              }
            }

          val prem = Select(M, x)
          val concl = Exists(List(i_), i_ === x && And(modified.toList))

          prem ==> concl
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
          case Succ(`i`) => true
          case Succ(j) if i == j => true // same as line above
          case _       => false
        }

        // TODO: how to rename variables
        val j = Var("j", Sort.int)
        val re = Expr.subst(i_ -> j)
        val renamed_inv = inv rename re

        val inv_ = inv && And(which) && And(how)

        val prog_ = While(test, body_, term, inv_, sum, frames)

        // prepare states after the loop
        // from or via here?
        val to = assume(via, inv_ && !test)
        /*
        println("prog_ " + prog_)
        println("to " + to)
        println()
         */
        (prog_, to)
    }
  }
}

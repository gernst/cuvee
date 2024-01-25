package cuvee.imp

import cuvee.pure._
import cuvee.smtlib._
import cuvee.pipe.Stage
import scala.collection.immutable

object Annotate extends Stage {
  case class State(path: List[Expr], vars: Map[Var, Expr])

  def exec(
      prefix: List[Cmd],
      cmds: List[Cmd],
      last: Cmd,
      state: cuvee.State
  ) = {
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
        val x = Expr.fresh(Var("x", Sort.int))

        def isModifiedArray(a: Var) = a.typ match {
          case Sort(Con.array, _) if mod.contains(a) => true
          case _                                     => false
        }

        // TODO: use this in the characterization of M
        def indexEqualities(a: Var, rhs: Expr, re: Map[Var, Var]): Expr =
          rhs match {
            case Store(`a`, key, _) =>
              val m = mOf(key)
              val key_ = key rename re
              val here = m.toExpr(x) && (x === key_)
              here

            case Store(rhs_, key, _) =>
              val m = mOf(key)
              val key_ = key rename re
              val here = m.toExpr(x) && (x === key_)
              val there = indexEqualities(a, rhs_, re)
              here || there
          }

        // TODO: use this characterization for the update
        def assignmentEqualities(a: Var, rhs: Expr): Expr =
          rhs match {
            case Store(`a`, key, value) =>
              val value_ = maybeOldOtherArrays(value)
              val here = (x === key) && (Select(a, x) === value_)
              here

            case Store(rhs_, key, value) =>
              val value_ = maybeOldOtherArrays(value)
              val here = (x === key) && (Select(a, x) === value_)
              val there = (x !== key) && assignmentEqualities(a, rhs_)
              here || there
          }

        def maybeOldOtherArrays(rhs: Expr): Expr = rhs topdown {
          // case Select(b: Var, key) =>
          //   Select(Ite(key in Mb, b, Old(b)), maybeOldOtherArrays(key))
          case Select(b: Var, key) if mod contains b =>
            Select(Old(b), maybeOldOtherArrays(key))
          case expr =>
            expr
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

        /** Provides a list of all variables occuring in the test
          *
          * @return
          *   List of Var used in the test
          */
        def testVars() = test match {
          case App(_, args)
              if args
                .forall(e => e.isInstanceOf[Var] || e.isInstanceOf[Lit]) =>
            for (e <- args if e.isInstanceOf[Var]) yield e.asInstanceOf[Var]
          case _ =>
            cuvee.error("Currently only simple tests are supported.")
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
          case n @ Var(_, Sort.int) =>
            val x0 = init(n)

            val candidates = mod.filter(v => v.typ == Sort.int)
            val testVars_ = testVars.toSet
            val List(dec) = candidates.intersect(testVars_).toList.distinct

            val stepxs = after map { st => st.vars(dec) }
            val List(step) = stepxs.distinct

            step match {
              case Plus(List(`n`, One)) | Plus(List(One, `n`)) =>
                Modified(x0, n, test)
              case Minus(`n`, One) =>
                Modified(n, x0, test)
              case _ =>
                cuvee.error("Currently only dense steps are supported.")
            }
          case c @ Lit(_, Sort.int) =>
            Modified(c, c, Le(c, c))
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

        /* Try to derive an invariant for a given while loop possibly
         * containing assignments to array.
         *
         * In case of an assignment to an array the utilized approach consists
         * of the collection of all modified indices and an observation, in
         * which way an array got modified.
         */
        val derive = for (st <- after) yield {
          val path = And(st.path)
          val arrays = st.vars.keySet filter isModifiedArray

          val all = for ((a, rhs) <- st.vars if arrays contains a) yield {
            val vars = mod -- arrays
            val (vars1, re1) = fresh(vars.toList)
            val (vars2, re2) = fresh(vars.toList)

            val prem = inv && test
            val prem_ = prem rename re1
            val phi = Exists(vars1, prem_ && indexEqualities(a, rhs, re1))

            val concl = inv && test && assignmentEqualities(a, rhs)
            val concl_ = concl rename re2
            val yes = Exists(vars2, concl_)

            // Every index which got not visited should not be modified
            val no = Select(a, x) === Old(Select(a, x))

            (phi ==> yes) && (!phi ==> no)
          }
          path ==> Forall(List(x), And(all.toList))
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
  * @param test
  *   the test from the loop needed for the boundary expression
  * @param step
  *   in which the indices change e.g. One for i := i + 1 and Two for i := i + 2
  *   Can also hold more complicated calculations. However: The expression are *
  *   held as is and will not be simplified
  */
sealed case class Modified(lb: Expr, ub: Expr, test: Expr, step: Expr = One) {

  /** Provides an expression describing all indices which got changed to place
    * into an invariant
    *
    * @param x
    *   an arbitrary integer to reason about the boundings in this instance
    * @return
    *   one expression containing all necessary informations which indices got
    *   changed
    */
  def toExpr(x: Expr): Expr = test match {
    case Lt(_, _) => lb <= x && x < ub
    case Le(_, _) => lb <= x && x <= ub
    case Gt(_, _) => lb < x && x < ub
    case Ge(_, _) => lb < x && x <= ub
    case _ =>
      cuvee.error(
        "Currently only tests with <=, <, >, >= are supported. Got: " + test
      )
  }
}

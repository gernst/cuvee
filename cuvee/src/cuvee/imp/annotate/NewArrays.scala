package cuvee.imp.annotate

import cuvee.pure._
import cuvee.imp._
import cuvee.smtlib.Solver
import cuvee.State

case object NewArrays extends Annotate(ExecNoLoops) {
  def while_(
      state: cuvee.State,
      paths: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv0: Expr,
      sum: Expr,
      frames: List[Frame]
  ) = {
    val mod = body.mod
    val read = body.read

    val (as, ys) = mod.toList partition {
      case a @ Var(_, Sort(Con.array, _)) => true
      case _                              => false
    }

    val vars = test.free ++ mod ++ read
    val xs = vars.toList

    val (cmds, before, after, body_) =
      iter(state, paths, xs, test, body, term, inv0, sum, frames)

    val counters = Accelerate.counters(paths.running, after.running, ys)

    val re = Expr.fresh(ys)
    val ys_ = ys rename re

    val lbs = Accelerate.lbsFromCounter(counters)
    val (ub, decreases) = Accelerate.ubAndDecreaseFromTest(And.flatten(test))

    for (
      (x, Kounter(init, step)) <- counters;
      phi <- And.flatten(test)
    )
      (init, phi) match {
        // bounded loops can be verified with BMC

        // case (_: Lit, Le(`x`, _: Lit)) if step > 0 =>
        //   cuvee.error("bounded loop: " + phi)
        // case (_: Lit, Lt(`x`, _: Lit)) if step > 0 =>
        //   cuvee.error("bounded loop: " + phi)
        // case (_: Lit, Ge(`x`, _: Lit)) if step < 0 =>
        //   cuvee.error("bounded loop: " + phi)
        // case (_: Lit, Gt(`x`, _: Lit)) if step < 0 =>
        //   cuvee.error("bounded loop: " + phi)
        case _ =>
      }

    val lockstep = Accelerate.lockstepCounters(counters)
    val inv = inv0 && And(lockstep)

    val prems = Accelerate.tryEarlierValuesOf(counters, ys, re)

    val avoids =
      for (
        Path(fresh, constraints, _, _) <-
          after.breaked ++ after.returned
      ) yield {
        val exit = Exists(fresh, And(constraints))
        Not(exit rename re)
      }

    val cases =
      for (path @ Path(fresh, constraints, stack, old) <- after.running)
        yield {
          // println(path)
          val pairs =
            for (a @ Var(name, Sort(Con.array, List(dom, ran))) <- as if (path lookup a) != a)
              yield {
                // XXX: collapses multiple stores to the same location (for array_init_increm_twice.c)
                val rhs = Simplify.simplify(path lookup a, state)
                val rhs_ = rhs rename re

                val eq_ = rhs match {
                  // Note: subsumed by the code below using assignmentEqualities,
                  //       kept for reference and potentially for debugging

                  // case Store(`a`, index, value) =>
                  //   val index_ = index rename re
                  //   val value_ = maybeOldOtherArrays(mod, value rename re)
                  //   val yes = Select(a, index_) === value_
                  //   val no = Select(a, index_) === Select(Old(a), index_)

                  //   (yes, no)

                  case _ =>
                    // val pairs1 = assignmentEqualities(mod, counters, re, a, Nil, rhs)

                    def untangle(index: Expr, value: Expr): (List[Expr], Expr) = value match {
                      case Store(
                            _,
                            index_,
                            value_
                          ) => // note: can ignore base and index in this context
                        val (indices, result) = untangle(index_, value_)
                        (index :: indices, result)
                      case _ =>
                        (List(index), value)
                    }

                    val (base: Var, updates) = Store.flatten(rhs_)
                    val todo = for ((i, v) <- updates) yield untangle(i, v)
                    val pairs2 = assignmentEqualities(mod, counters, base, Nil, todo)

                    // println(pairs1)
                    // println(pairs2)

                    // assert(pairs1 == pairs2)

                    val (yes, no) = pairs2.unzip
                    (And(yes), And(no))
                }

                eq_
              }

          val (eqs_, neqs_) = pairs.unzip
          val constraints_ = constraints rename re
          (Exists(fresh, And(constraints_ ++ eqs_)), Forall(fresh, And(neqs_)))
        }

    val (updated, frame) = cases.unzip
    val prems_ = (inv rename re) :: prems

    val phi = Forall(ys_, And(prems_) ==> Or(updated))
    val psi = Forall(ys_, ((inv rename re) && !And(prems)) ==> And(frame))
    val chi = Forall(ys_, And(prems_) ==> And(avoids))

    // TODO: evaluation/earlier/sv-benchmarks/standard_vararg_ground.annotated.bpl
    //       does not have a loop test that involves counters so ub is wrong
    val inv_ = inv && And(lockstep) && And(lbs) && /* ub && */ phi && psi && chi
    val inv__ = Simplify.simplify(inv_, state)

    // println("lb: " + lbs)
    // println("ub: " + ub)

    var term_ = if (term == Zero) decreases else term

    val prog_ = While(test, body_, term_, inv__, sum, frames)
    val paths_ = exec.spec(paths, mod.toList, inv__, inv__ && !test)

    (cmds, paths_, prog_)
  }

  def maybeOldOtherArrays(mod: Set[Var], rhs: Expr): Expr = rhs topdown {
    case Select(b: Var, key) if mod contains b =>
      Select(Old(b), maybeOldOtherArrays(mod, key))
    case expr =>
      expr
  }

  def assignmentEqualities(
      mod: Set[Var],
      counters: Map[Var, Kounter],
      re: Map[Var, Var],
      a: Var,
      overwritten: List[Expr],
      rhs: Expr
  ): List[(Expr, Expr)] =
    rhs match {
      case `a` =>
        Nil

      case Store(rhs_, index, value) =>
        val index_ = index rename re
        val value_ = maybeOldOtherArrays(mod, value rename re)

        var yes = Select(a, index_) === value_
        var no = Select(a, index_) === Select(Old(a), index_)

        if (overwritten.nonEmpty) {
          val prems = overwritten map (index_ !== _)
          yes = And(prems) ==> yes
        }

        val there = assignmentEqualities(mod, counters, re, a, index_ :: overwritten, rhs_)

        (yes, no) :: there

      case other =>
        cuvee.error("multidimensional arrays are not supported")
    }

  // this one works on renamed done/todo already
  def assignmentEqualities(
      mod: Set[Var],
      counters: Map[Var, Kounter],
      base: Var,
      done: List[List[Expr]],
      todo: List[(List[Expr], Expr)]
  ): List[(Expr, Expr)] = todo match {
    case Nil =>
      Nil

    case (indices, value) :: rest =>
      var yes = Select(base, indices) === maybeOldOtherArrays(mod, value)
      val no = Select(base, indices) === Select(Old(base), indices)

      if (done.nonEmpty) {
        val prems =
          for (
            indices_ <- done;
            (i, i_) <- indices zip indices_
          )
            yield i !== i_
        yes = And(prems) ==> yes
      }

      val there = assignmentEqualities(mod, counters, base, indices :: done, rest)
      (yes, no) :: there
  }
}

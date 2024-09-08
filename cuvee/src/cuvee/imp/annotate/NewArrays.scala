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
      inv: Expr,
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

    val (before, after, body_) =
      iter(state, paths, xs, test, body, term, inv, sum, frames)

    val counters = Accelerate.counters(paths.running, after.running, ys)

    val re = Expr.fresh(ys)
    val ys_ = ys rename re

    val lbs = Accelerate.lbsFromCounter(counters)
    val (ub, decreases) = Accelerate.ubAndDecreaseFromTest(And.flatten(test))

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
          val pairs =
            for (a @ Var(name, Sort(Con.array, List(dom, ran))) <- as if (path lookup a) != a)
              yield {
                // XXX: collapses multiple stores to the same location (for array_init_increm_twice.c)
                val rhs = path lookup a // Simplify.simplify(path lookup a, Map(), Set())

                val eq_ = rhs match {
                  case Store(`a`, index, value) =>
                    val index_ = index rename re
                    val value_ = maybeOldOtherArrays(mod, value rename re)
                    val yes = Select(a, index_) === value_
                    val no = Select(a, index_) === Select(Old(a), index_)

                    (yes, no)
                }

                eq_
              }

          val (eqs_, neqs_) = pairs.unzip
          val constraints_ = constraints rename re
          (Exists(fresh, And(constraints_ ++ eqs_)), And(neqs_))
        }

    val (updated, frame) = cases.unzip

    val phi = Forall(ys_, And(prems) ==> Or(updated))
    val psi = Forall(ys_, !And(prems) ==> And(frame))
    val chi = Forall(ys_, And(prems) ==> And(avoids))
    val inv_ = inv && And(lbs) && ub && phi && psi && chi

    val prog_ = While(test, body_, term, inv_, sum, frames)
    val paths_ = exec.spec(paths, mod.toList, inv_, inv_ && !test)

    (paths_, prog_)
  }

  def maybeOldOtherArrays(mod: Set[Var], rhs: Expr): Expr = rhs topdown {
    case Select(b: Var, key) if mod contains b =>
      Select(Old(b), maybeOldOtherArrays(mod, key))
    case expr =>
      expr
  }
}

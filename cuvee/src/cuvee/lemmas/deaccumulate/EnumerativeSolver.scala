package cuvee.lemmas.deaccumulate

import cuvee.State
import cuvee.pure._
import cuvee.smtlib.Solver
import cuvee.lemmas.Enumerate

class EnumerativeSolver(
    funs: List[Fun],
    occur: Int,
    depth: Int,
    state: State,
    solver: Solver,
    rws: Map[Fun, List[Rule]]
) extends IncrementalSolver(state, solver, rws) {

  def suggest(n: N) = {
    cuvee.error("use enumerative solver currently supported only after heuristic guesses")
  }

  def suggest(g: G) = {
    cuvee.error("use enumerative solver currently supported only after heuristic guesses")
  }

  def suggest(cond: B) = {
    val B(formals, f, args, lhs, rhs, guard) = cond
    // find body which occurs in both lhs and rhs with different arguments
    // such that forall formals: lhs == rhs if guard
    // we may use args to define this function

    val base = Map(args map ((_: Expr) -> occur): _*)

    ??? // this won't get checked!
    for ((body, _) <- Enumerate.enumerate(f.res, funs, base, depth))
      yield (List(D(args, f, body)), Nil)
  }
}

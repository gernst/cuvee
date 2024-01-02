package cuvee.lemmas.deaccumulate

import cuvee.State
import cuvee.smtlib._
import cuvee.pure._

class HeuristicSolver(
    neutral: List[Either[(Fun, Expr), (Fun, Expr)]],
    solver: Solver,
    state: State,
    rws: Map[Fun, List[Rule]]
) extends IncrementalSolver(state, solver, rws) {

  def suggest(g: G) = {
    val G(formals, f, body) = g
    val d = D(formals, f, body)
    List((List(d), Nil, Nil))
  }

  def suggest(b: B) = {
    List((Nil, Nil, List(b)))
  }

  def suggest(n: N) = {
    val N(z, o, b) = n
    val xs = Expr.vars("x", o.args)

    neutral map {
      case Left((f, e)) if f.res == o.res =>
        assert(f.args == o.args)
        val d1 = D(Nil, b, e)
        val d2 = D(xs, o, App(f, xs))
        (List(d1, d2), Nil, Nil)

      case Right((f, e)) if f.res == o.res =>
        assert(f.args.reverse == o.args)
        val d1 = D(Nil, b, e)
        val d2 = D(xs, o, App(f, xs.reverse))
        (List(d1, d2), Nil, Nil)

      case _ =>
        (Nil, Nil, List(n))
    }
  }
}

package cuvee.lemmas.deaccumulate

import cuvee.State
import cuvee.smtlib._
import cuvee.pure._

class HeuristicSolver(
    neutral: List[Either[(Fun, Expr), (Fun, Expr)]],
    solver: Solver,
    state: State,
    rws: Map[Fun, List[Rule]]
) extends QuerySolver {
  val constrs = state.constrs

  def solve(query: Query) = {
    val Query(df, args, df_, rhs, oplus, unknowns, conds) = query

    val defs = conds collect { case c: D => c }
    val base = conds collect { case c: N => c }
    val easy = conds collect { case c: A => c }
    val guess = conds collect { case c: G => c }
    val hard = conds collect { case c: B => c }
    assert(easy.isEmpty, "internal error: all easy cases should be presented as guesses instead")

    val rules = Nil

    for (
      (unknowns_, conds_, rules, rws_) <- solve(unknowns, defs, base, easy, guess, hard, rules, rws)
    )
      yield (Query(df, args, df_, rhs, oplus, unknowns_, conds_), rules)
  }

  def check(
      unknowns: Set[Fun],
      easy: List[A],
      hard: List[B],
      rws: Map[Fun, List[Rule]]
  ): List[(List[A], List[B])] = {
    val (check1, easy_) =
      easy partition (_.funs disjoint unknowns)
    val (check2, hard_) =
      hard partition (_.funs disjoint unknowns)

    val phis =
      for (cond <- check1 ++ check2)
        yield Simplify.simplify(cond.toExpr, rws, constrs)

    if (phis forall solver.isTrue) {
      List((easy_, hard_))
    } else {
      Nil
    }
  }

  def check(
      unknowns: Set[Fun],
      easy: List[A],
      guess: List[G],
      hard: List[B],
      rules: List[Rule],
      rws: Map[Fun, List[Rule]]
  ): List[(Set[Fun], List[Cond], List[Rule], Map[Fun, List[Rule]])] = {
    for (
      (easy_, hard_) <- check(unknowns, easy, hard, rws);
      result <- solve(unknowns, easy_, guess, hard_, rules, rws)
    )
      yield result
  }

  def solve(
      unknowns: Set[Fun],
      easy: List[A],
      guess: List[G],
      hard: List[B],
      rules: List[Rule],
      rws: Map[Fun, List[Rule]]
  ): List[(Set[Fun], List[Cond], List[Rule], Map[Fun, List[Rule]])] = {
    (guess, hard) match {
      case (Nil, _) =>
        // currently no support for solving hard queries,
        // also collect remaining easy assertions
        List((unknowns, easy ++ hard, rules, rws))

      case (G(formals, f, body) :: rest, _) =>
        assert(!(unknowns contains f))
        val eq = Rule(App(f, formals), body)
        val rws_ = rws + (f -> List(eq))
        // don't check now because likely the body is not resolved yet
        check(unknowns - f, easy, rest, hard, eq :: rules, rws_)
    }
  }

  def solve(
      unknowns: Set[Fun],
      defs: List[D],
      base: List[N],
      easy: List[A],
      guess: List[G],
      hard: List[B],
      rules: List[Rule],
      rws: Map[Fun, List[Rule]]
  ): List[(Set[Fun], List[Cond], List[Rule], Map[Fun, List[Rule]])] = {
    (defs, base) match {
      case (Nil, Nil) =>
        solve(unknowns, easy, guess, hard, rules, rws)

      // eagerly substitute definitional constraints
      case (D(args, f, body) :: rest, _) if unknowns contains f =>
        val eq = Rule(App(f, args), body)
        val rws_ = rws + (f -> List(eq))
        // don't check now because likely the body is not resolved yet
        solve(unknowns - f, rest, base, easy, guess, hard, eq :: rules, rws_)

      // but if the function has been defined, convert into assertion
      case (D(args, f, body) :: rest, _) =>
        val cond = A(args, App(f, args), body, True)
        solve(unknowns, defs, base, cond :: easy, guess, hard, rules, rws)

      // next: try to instantiate base cases with operators that have neutral elements
      case (Nil, N(z, o, b) :: rest) =>
        require(unknowns contains o, "already solved for " + o)
        require(unknowns contains b, "already solved for " + b)

        // create two equations, one for b and one for o,
        // represent as D queries for uniformity

        val xs = Expr.vars("x", o.args)

        val options =
          neutral map {
            case Left((f, e)) if f.res == o.res =>
              assert(f.args == o.args)
              val d1 = D(Nil, b, e)
              val d2 = D(xs, o, App(f, xs))
              List(d1, d2)

            case Right((f, e)) if f.res == o.res =>
              assert(f.args.reverse == o.args)
              val d1 = D(Nil, b, e)
              val d2 = D(xs, o, App(f, xs.reverse))
              List(d1, d2)

            case _ =>
              Nil
          }

        for (
          conds <- options;
          result <- solve(unknowns, conds ++ defs, base, easy, guess, hard, rules, rws)
        )
          yield result
    }
  }
}

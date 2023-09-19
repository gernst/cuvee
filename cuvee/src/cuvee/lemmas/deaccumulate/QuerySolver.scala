package cuvee.lemmas.deaccumulate

import cuvee.State
import cuvee.pure._
import cuvee.smtlib.Solver

trait QuerySolver {
  def solve(query: Query): List[(Query, List[Rule])]
}

abstract class IncrementalSolver(state: State, solver: Solver, rws: Map[Fun, List[Rule]])
    extends QuerySolver {
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
    val kept = Nil

    for (
      (unknowns_, conds_, rules, rws_) <- solve(
        unknowns,
        defs,
        base,
        guess,
        easy,
        hard,
        kept,
        rules,
        rws
      )
    )
      yield (Query(df, args, df_, rhs, oplus, unknowns_, conds_), rules)
  }

  def suggest(n: N): List[(List[D], List[Cond])]
  def suggest(g: G): List[(List[D], List[Cond])]
  def suggest(b: B): List[(List[D], List[Cond])]

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
      defs: List[D],
      base: List[N],
      guess: List[G],
      easy: List[A],
      hard: List[B],
      kept: List[Cond],
      rules: List[Rule],
      rws: Map[Fun, List[Rule]]
  ): List[(Set[Fun], List[Cond], List[Rule], Map[Fun, List[Rule]])] = {
    for (
      (easy_, hard_) <- check(unknowns, easy, hard, rws);
      result <- solve(unknowns, defs, base, guess, easy_, hard_, kept, rules, rws)
    )
      yield result
  }

  def solve(
      unknowns: Set[Fun],
      defs: List[D],
      base: List[N],
      guess: List[G],
      easy: List[A],
      hard: List[B],
      kept: List[Cond],
      rules: List[Rule],
      rws: Map[Fun, List[Rule]]
  ): List[(Set[Fun], List[Cond], List[Rule], Map[Fun, List[Rule]])] = {
    (defs, base, guess, easy, hard) match {
      case (Nil, Nil, Nil, Nil, Nil) =>
        List((unknowns, kept, rules, rws))

      // eagerly substitute definitional constraints
      case (D(args, f, body) :: rest, _, _, _, _) if unknowns contains f =>
        val eq = Rule(App(f, args), body)
        val rws_ = rws + (f -> List(eq))
        // don't check now because likely the body is not resolved yet
        check(unknowns - f, rest, base, guess, easy, hard, kept, eq :: rules, rws_)

      // but if the function has been defined, convert into assertion
      case (D(args, f, body) :: rest, _, _, _, _) =>
        val cond = A(args, App(f, args), body, True)
        solve(unknowns, defs, base, guess, cond :: easy, hard, kept, rules, rws)

      // next: try to instantiate base cases with operators that have neutral elements
      case (Nil, n :: rest, _, _, _) =>
        for (
          (conds, kept_) <- suggest(n);
          funs = conds flatMap (_.funs);
          result <- solve(
            unknowns -- funs,
            conds ++ defs,
            rest,
            guess,
            easy,
            hard,
            kept_,
            rules,
            rws
          )
        )
          yield result

      case (Nil, Nil, g :: rest, _, _) =>
        for (
          (conds, kept_) <- suggest(g);
          funs = conds flatMap (_.funs);
          result <- solve(
            unknowns -- funs,
            conds ++ defs,
            base,
            rest,
            easy,
            hard,
            kept_,
            rules,
            rws
          )
        )
          yield result

      case (Nil, Nil, Nil, _, b :: rest) =>
        for (
          (conds, kept_) <- suggest(b);
          funs = conds flatMap (_.funs);
          result <- solve(
            unknowns -- funs,
            conds ++ defs,
            base,
            guess,
            easy,
            rest,
            kept_,
            rules,
            rws
          )
        )
          yield result
    }
  }
}

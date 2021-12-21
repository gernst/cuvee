package cuvee.lemmas

import cuvee.pure._

object Split {
  def maybeShift(e: Expr) =
    e match {
      case App(_, _, args) if args.nonEmpty =>
        val a = Expr.fresh("a", e.typ)
        (a, List(a -> e))
      case _ =>
        (e, Nil)
    }

  def maybeShift(er: (Expr, Boolean), cs: List[(Var, Expr)]) =
    er match {
      case (e @ App(_, _, args), false) if args.nonEmpty =>
        val c = Expr.fresh("c", e.typ)
        (c, List(c -> e))
      case (e, _) =>
        (e, cs)
    }

  def splits(
      f: Fun,
      exprs: Expr*
  ): (
      (List[Expr], Boolean),
      (List[(Var, Expr)], List[(Var, List[Expr])], List[(Var, Expr)])
  ) = {
    val results = exprs.toList map (split(f, _))
    val (es, lets) = results.unzip
    val (as, bs, cs) = lets.unzip3

    val shift = es exists (_._2)

    if (shift) {
      // now shift all non-recursive exprs to the map,
      // these are maximally non-recursive subterms
      val es_cs =
        for ((er, c) <- es zip cs)
          yield maybeShift(er, c)

      val (es_, cs_) = es_cs.unzip
      ((es_, true), (as.flatten, bs.flatten, cs_.flatten))
    } else {
      val (es_, lets) = es.unzip
      ((es_, false), (as.flatten, bs.flatten, cs.flatten))
    }
  }

  def split(
      f: Fun,
      expr: Expr
  ): (
      (Expr, Boolean),
      (List[(Var, Expr)], List[(Var, List[Expr])], List[(Var, Expr)])
  ) =
    expr match {
      case App(`f`, inst, args) =>
        val es_as =
          for (e <- args)
            yield maybeShift(e)
        val (args_, as) = es_as.unzip

        val b = Expr.fresh("b", expr.typ)
        ((b, true), (as.flatten, List(b -> args_), Nil))

      case App(g, inst, args) =>
        val ((args_, rec), let) = splits(f, args: _*)
        val expr_ = App(g, inst, args_)
        ((expr_, rec), let)

      case _ =>
        ((expr, false), (Nil, Nil, Nil))
    }

  def norm(f: Fun, expr: Expr): Norm = {
    val ((e, r), (as, bs, cs)) = split(f, expr)
    // val (e_, cs_) = maybeShift((e, r), cs) // shift if not recursive
    Norm(as, bs, cs, e)
  }

  def rw(
      xs: List[Var],
      guard: List[Expr],
      lhs: App,
      rhs: Expr,
      st: State
  ): List[(Fun, Case)] =
    (lhs, rhs) match {
      case (App(fun, _, args), Ite(test, left, right)) =>
        val l = rw(xs, test :: guard, lhs, left, st)
        val r = rw(xs, Not(test) :: guard, lhs, right, st)
        l ++ r

      case (App(fun, _, args), rhs) =>
        List((fun, Case(xs, args, guard, norm(fun, rhs))))

      case _ =>
        Nil
    }

  def rw(expr: Expr, st: State): List[(Fun, Case)] =
    expr match {
      case Clause(xs, ant, Eq(lhs: App, rhs)) =>
        rw(xs, ant, lhs, rhs, st)

      case _ =>
        Nil
    }

  def rw(exprs: List[Expr], st: State): List[(Fun, Case)] = {
    for (
      expr <- exprs;
      rule <- rw(expr, st)
    )
      yield rule
  }
}

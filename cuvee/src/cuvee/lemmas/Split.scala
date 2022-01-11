package cuvee.lemmas

import cuvee.pure._

import cuvee.ListMapOps

object Split {
  def maybeShift(e: Expr): (Expr, Map[Var, Expr]) =
    e match {
      case App(_, _, args) if args.nonEmpty =>
        val a = Expr.fresh("a", e.typ)
        (a, Map(a -> e))
      case _ =>
        (e, Map())
    }

  def maybeShift(
      er: (Expr, Boolean),
      cs: Map[Var, Expr]
  ): (Expr, Map[Var, Expr]) =
    er match {
      case (e @ App(_, _, args), false) if args.nonEmpty =>
        val c = Expr.fresh("c", e.typ)
        (c, Map(c -> e))
      case (e, _) =>
        (e, cs)
    }

  def splits(
      f: Fun,
      exprs: Expr*
  ): (
      (List[Expr], Boolean),
      (Map[Var, Expr], Map[Var, List[Expr]], Map[Var, Expr])
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
      ((es_, true), (as.merged, bs.merged, cs_.merged))
    } else {
      val (es_, lets) = es.unzip
      ((es_, false), (as.merged, bs.merged, cs.merged))
    }
  }

  def split(
      f: Fun,
      expr: Expr
  ): (
      (Expr, Boolean),
      (Map[Var, Expr], Map[Var, List[Expr]], Map[Var, Expr])
  ) =
    expr match {
      case App(`f`, inst, args) =>
        val es_as =
          for (e <- args)
            yield maybeShift(e)
        val (args_, as) = es_as.unzip

        val b = Expr.fresh("b", expr.typ)
        ((b, true), (as.merged, Map(b -> args_), Map()))

      case App(g, inst, args) =>
        val ((args_, rec), let) = splits(f, args: _*)
        val expr_ = App(g, inst, args_)
        ((expr_, rec), let)

      case _ =>
        ((expr, false), (Map(), Map(), Map()))
    }

  def split(df: Def[Flat]): Def[Norm] = {
    val Def(f, cases) = df

    val cases_ =
      for (Flat(args, guard, body) <- cases)
        yield {
          val ((d, r), (as, bs, cs)) = split(f, body)
          Norm(args, guard, as, bs, cs, d)
        }

    Def(f, cases_)
  }
}

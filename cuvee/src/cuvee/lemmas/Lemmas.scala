package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._

object test extends Run(Lemmas, "examples/list-defs.smt2")

case class Norm(rec: List[(Var, Expr)], map: List[(Var, Expr)], res: Expr)

case class Case(
    xs: List[Var],
    args: List[Expr],
    guard: List[Expr],
    rhs: Norm
)

object Lemmas extends Main {
  var eqs: Map[Fun, Expr] = Map()

  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)

    val eqs0 =
      for (
        Assert(expr) <- cmds;
        eq <- rw(expr, st)
      )
        yield eq

    val eqs1 = eqs0.groupBy(_._1)

    for ((fun, cases) <- eqs1)
      show(fun, cases)
  }

  def show(fun: Fun, cases: List[(Any, Case)]) {
    println(fun)
    for ((_, Case(xs, args, guard, Norm(rec, map, res))) <- cases) {
      print("  case " + args.mkString("(", ", ", ")"))
      if (guard.nonEmpty)
        print(" if " + guard.mkString(" /\\ "))
      println(" -> ")
      for ((a, r) <- rec)
        println("  let  " + a + " = " + r)
      for ((a, m) <- map)
        println("  let  " + a + " = " + m)
      println("       " + res)
    }
    println()
  }

  def maybeShift(fold: (Expr, Boolean), map: List[(Var, Expr)]) =
    fold match {
      case (e: App, false) =>
        val w = Expr.fresh("w", e.typ)
        (w, List(w -> e))
      case (e: Lit, false) =>
        val w = Expr.fresh("w", e.typ)
        (w, List(w -> e))
      case (e, _) =>
        (e, map)
    }

  def splits(
      f: Fun,
      exprs: Expr*
  ): ((List[Expr], Boolean), List[(Var, Expr)], List[(Var, Expr)]) = {
    val results = exprs.toList map (split(f, _))
    val (exprs_, recs, maps) = results.unzip3

    val shift = exprs_ exists (_._2)

    if (shift) {
      // now shift all non-recursive exprs to the map,
      // these are maximally non-recursive subterms
      val exprs_maps =
        for ((er, map) <- exprs_ zip maps)
          yield maybeShift(er, map)

      val (es, maps_) = exprs_maps.unzip
      ((es, true), recs.flatten, maps_.flatten)
    } else {
      val (es, _) = exprs_.unzip
      ((es, false), recs.flatten, maps.flatten)
    }
  }

  def split(
      f: Fun,
      expr: Expr
  ): ((Expr, Boolean), List[(Var, Expr)], List[(Var, Expr)]) =
    expr match {
      case App(`f`, inst, args) =>
        val u = Expr.fresh("u", expr.typ)
        ((u, true), List(u -> expr), Nil)

      case App(g, inst, args) =>
        val ((args_, rec), recs, maps) = splits(f, args: _*)
        val expr_ = App(g, inst, args_)
        ((expr_, rec), recs, maps)

      case _ =>
        ((expr, false), Nil, Nil)
    }

  def norm(f: Fun, expr: Expr): Norm = {
    val ((e, r), rec, map) = split(f, expr)
    val (e_, map_) = maybeShift((e, r), map) // shift if not recursive
    Norm(rec, map_, e_)
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

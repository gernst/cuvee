package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._
import cuvee.StringOps

case class Case(
    args: List[Expr],
    guard: List[Expr],
    as: Map[Var, Expr],
    bs: Map[Var, List[Expr]],
    cs: Map[Var, Expr],
    d: Expr
) {
  def free = args.free
  def isBaseCase = bs.isEmpty

  def prime = {
    val re = Expr.subst(free map (x => (x, x.prime)))
    val as_ = as map { case (a, e) => (a, e rename re) }
    val bs_ = bs map { case (b, e) => (b, e rename re) }
    val cs_ = cs map { case (c, e) => (c, e rename re) }

    Case(
      args rename re,
      guard rename re,
      as_,
      bs_,
      cs_,
      d rename re
    )
  }
}

case class Def(fun: Fun, cases: List[Case]) {
  for (Case(args, guard, as, bs, cs, d) <- cases) {
    require(
      fun.args == args.types,
      "type mismatch: " + fun + " applied to " + args
    )
    require(fun.res == d.typ, "type mismatch: " + fun)
  }
}

object _1 extends Run(Lemmas, "examples/1.smt2")
object _2 extends Run(Lemmas, "examples/2.smt2")
object _3 extends Run(Lemmas, "examples/3.smt2")
object _4 extends Run(Lemmas, "examples/4.smt2")
object test1 extends Run(Lemmas, "examples/list-defs.smt2")
object test2 extends Run(Lemmas, "examples/list-fused.smt2")

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
        eq <- Split.rw(expr, st)
      )
        yield eq

    val eqs1 =
      for ((fun, stuff) <- eqs0.groupBy(_._1))
        yield {
          val (_, cases) = stuff.unzip
          Def(fun, cases)
        }

    for (df <- eqs1) {
      show(df)

      val us = Util.usedArgs(df)
      val ka = Util.constantArgs(df)
      val kc = Util.computedArgs(df)
      val kr = Util.constantResults(df, ka)
      // println("used arguments:     " + xs)
      // println("constant arguments: " + ys)
      // println("constant results:   " + zs)

      if (kr.nonEmpty) {
        val (df_, dfa, eq) = Factor.base(df, kr)
        show(df_)
        for (df <- dfa)
          show(df)
        show(eq)

        Lift.lift(df_)
      }

      // val dfs_a = Factor.arguments(df, kc)

      // for (df_a <- dfs_a)
      //   show(df_a)
    }
  }

  def show(r: Rule) {
    println(r)
    println()
  }

  def show(df: Def) {
    val Def(fun, cases) = df
    println(fun)

    for (Case(args, guard, as, bs, cs, d) <- cases) {
      print("  case " + args.mkString("(", ", ", ")"))
      if (guard.nonEmpty)
        print(" if " + guard.mkString(" /\\ "))
      println(" -> ")
      for ((x, e) <- as)
        println("    let " + x + " = " + e)
      for ((x, es) <- bs)
        println("    let " + x + " = " + App(fun, es))
      for ((x, e) <- cs)
        println("    let " + x + " = " + e)
      println("    in  " + d)
    }
    println()
  }
}

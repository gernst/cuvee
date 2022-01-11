package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._
import cuvee.StringOps

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
        eq <- Def.rw(expr, st)
      )
        yield eq

    val eqs1 =
      for ((fun, stuff) <- eqs0.groupBy(_._1))
        yield {
          val (_, cases) = stuff.unzip
          Def(fun, cases)
        }

    for (df <- eqs1; dg <- eqs1) {
      for ((dfg, eq) <- Fuse.fuse(df, dg)) {
        show(dfg)
        show(eq)
      }
    }

    for (df0 <- eqs1) {
      val df = Split.split(df0)

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

  def show(fun: Fun, cs: Case) {
    cs match {
      case Flat(args, guard, body) =>
        print("  case " + args.mkString("(", ", ", ")"))
        if (guard.nonEmpty)
          print(" if " + guard.mkString(" /\\ "))
        println(" -> ")
        println("    in  " + body)

      case Norm(args, guard, as, bs, cs, d) =>
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
  }

  def show(df: Def[Case]) {
    val Def(fun, cases) = df
    println(fun)
    for (cs <- cases)
      show(fun, cs)
    println()
  }
}

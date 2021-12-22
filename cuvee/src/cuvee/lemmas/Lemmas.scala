package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._
import cuvee.StringOps

case class Def(fun: Fun, cases: List[Case]) {
  for (Case(xs, args, guard, as, bs, cs, d) <- cases) {
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
    }

    for (df <- eqs1 if false) {
      show(df)

      val dfs_a = Norm.ana(df, st)

      for (df_a <- dfs_a)
        show(df_a)

      val df_b = Norm.rec(df, st)
      show(df_b)

      val (df_b_, eq_b) = Norm.lift(df_b, dfs_a, st)
      show(df_b_)

      println(eq_b)
      println()

      val df_cr = Norm.map(df, st)
      show(df_cr)

      val df_cb = Norm.base(df, st)
      show(df_cb)

      val (df_, eq_) = Norm.lift(df, df_cr, df_cb, st)
      show(df_)

      println(eq_)
      println()
    }
  }

  def show(r: Rule) {
    println(r)
    println()
  }

  def show(df: Def) {
    val Def(fun, cases) = df
    println(fun)

    for (Case(xs, args, guard, as, bs, cs, d) <- cases) {
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

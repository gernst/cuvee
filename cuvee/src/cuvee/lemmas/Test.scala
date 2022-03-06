package cuvee.lemmas

import cuvee.error
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._
import cuvee.StringOps

// object _1 extends Run(Test, "examples/1.smt2")
// object _2 extends Run(Test, "examples/2.smt2")
// object _3 extends Run(Test, "examples/3.smt2")
// object _4 extends Run(Test, "examples/4.smt2")
// object test1 extends Run(Test, "examples/list-defs.smt2")
// object test2 extends Run(Test, "examples/list-fused.smt2")

object Test extends Main {
  var eqs: Map[Fun, Expr] = Map()

  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)

    val lemma = new Lemma(st)
    val fuse = new Fuse(lemma)
    val factor = new Factor(lemma)

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

    // val fused = for (df <- eqs1; dg <- eqs1; (dfg, eq) <- fuse.fuse(df, dg)) yield {
    //   show(dfg)
    //   show(eq)
    //   dfg
    // }


    for (df0 <- eqs1) {
      val df = factor.split(df0)

      show(df)

      val us = Util.usedArgs(df)
      val ka = Util.constantArgs(df)
      val kc = Util.computedArgs(df)
      val kr = Util.constantResults(df, ka)
      // println("used arguments:     " + xs)
      // println("constant arguments: " + ys)
      println("constant results:   " + kr)

      if (kr.nonEmpty) {
        val (df_, dfa, eq) = factor.base(df)
        show(df_)
        for (df <- dfa)
          show(df)
        show(eq)

        val rules = Lift.lift(df_)
        for (r <- rules)
          show(r)
      }

      // val dfs_a = Factor.arguments(df, kc)

      // for (df_a <- dfs_a)
      //   show(df_a)
    }
  }

  def show_(r: Rule) {
    for (line <- r.lines)
      println(line)
    println()
  }

  def show(r: Rule) {
    println(r)
    println()
  }

  def show(fun: Fun, cs: CS) {
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

  def show_(df: Def[CS]) {
    val cmds = df.decl :: df.axioms
    for (line <- cmds.flatMap(_.lines))
      println(line)
    println()
  }

  def show(df: Def[CS]) {
    val Def(fun, cases) = df
    println(fun)
    for (cs <- cases)
      show(fun, cs)
    println()
  }
}

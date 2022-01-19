package cuvee.lemmas

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._

object _2 extends Run(Lemma, "examples/2.smt2")
object list_defs extends Run(Lemma, "examples/list-defs.smt2")

object Lemma extends Main {
  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)
    val lemma = new Lemma(st)
    lemma.seed(cmds)

    println("definitional rules")
    for (rule <- lemma.rules.defs)
      println(rule)
    println()

    println("fusion rules")
    for (rule <- lemma.rules.fuse)
      println(rule)
    println()

    println("normalization rules")
    for (rule <- lemma.rules.norm)
      println(rule)
    println()

    println("representation rules")
    for (rule <- lemma.rules.repr)
      println(rule)
    println()
  }
}

class Lemma(st: State) {

  object defs {
    // all original definitions
    var flat: Map[Fun, Def[Flat]] = Map()

    // fused function f.g where g is at f's given positional argument
    var fused: Map[(Fun, Fun, Int), Fun] = Map()

    // functions from flat which have been normalized
    var norm: Map[Fun, Def[Norm]] = Map()

    var known: Set[Fun] = Set()
  }

  // equivalences connecting the above functions
  object rules {
    var defs: List[Rule] = Nil
    var norm: List[Rule] = Nil
    var fuse: List[Rule] = Nil
    var repr: List[Rule] = Nil
  }

  // discovered lemmas
  var lemmas: List[Rule] = Nil

  val _factor = new Factor(st)
  val _fuse = new Fuse(st)
  val _known = new Known(st)

  def register(df: Def[Norm]) {
    defs.norm += df.fun -> df
    val eqs =
      _known.known(df, defs.norm.values filterNot (defs.known contains _.fun))
    if (eqs.nonEmpty)
      defs.known += df.fun
    rules.repr ++= eqs
  }

  def define(df: Def[Flat]) {
    val f = df.fun
    defs.flat += f -> df
    val eqs =
      for (cs <- df.cases)
        yield cs.rule(f)
    rules.defs ++= eqs
  }

  def factor(df: Def[Flat]) {
    val (df_, dfs, eqs) = _factor.factor(df)
    // cuvee.lemmas.Test.show(df_)
    register(df_)
    for (df <- dfs)
      register(df)
    rules.norm ++= eqs
  }

  def fuse(df: Def[Flat], dg: Def[Flat]) {
    val stuff = _fuse.fuse(df, dg)
    val (dhs, eqs) = stuff.unzip
    rules.fuse ++= eqs
    for (dh <- dhs) {
      // define(dh)
      factor(dh)
    }
  }

  def seed(cmds: List[Cmd]) {
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

    for (df <- eqs1) {
      define(df)
    }

    for ((f, df) <- defs.flat)
      factor(df)

    for ((f, df) <- defs.flat; (g, dg) <- defs.flat)
      fuse(df, dg)
  }
}

package cuvee.lemmas

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._

object _1 extends Run(Lemma, "examples/1.smt2")
object _2 extends Run(Lemma, "examples/2.smt2")
object _5 extends Run(Lemma, "examples/5.smt2")
object _6 extends Run(Lemma, "examples/6.smt2")
object _78 extends Run(Lemma, "benchmarks-smtlib/isaplanner/prop_78.smt2")
object _28 extends Run(Lemma, "benchmarks-smtlib/prod/prop_28.smt2")

object list_defs extends Run(Lemma, "examples/list-defs.smt2")

object debug extends Run(Lemma, "examples/debug.smt2")

object isaplanner
    extends Run(Lemma, "benchmarks-smtlib/isaplanner/prop_02.smt2")

object Lemma extends Main {
  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)
    val lemma = new Lemma(st)
    lemma.seed(cmds)
    lemma.prove(cmds)
    lemma.dump_rules()
  }
}

class Lemma(st: State) {
  def dump_rule(rule: Rule, as: List[Rule], bs: List[Rule]) {
    val Rule(lhs, rhs, cond, _) = rule
    val as_ = as.groupBy(_.fun)
    val bs_ = bs.groupBy(_.fun)
    val lhs_ = Rewrite.rewrite(lhs, as_)
    val rhs_ = Rewrite.rewrite(rhs, bs_)
    val cond_ = Rewrite.rewrite(cond, bs_)
    val rule_ = Rule(lhs_, rhs_, cond_)
    println(rule_)
    // val cmd = Assert(rule_.toExpr)
    // for(line <- cmd.lines)
    //   println(line)
    //   println()
  }

  def dump_rules() {
    val lhs = rules.fuse map (_.flip)
    val rhs = rules.repr ++ rules.norm ++ rules.defs // ++ rules.lift
    val rules_norm_ = rules.norm flatMap (_.maybeFlip)

    // rhs map println

    println("; normalization rules")
    for (rule <- rules.norm)
      dump_rule(rule, lhs, rhs)
    println()

    println("; lifting/propagation rules")
    for (rule <- rules.lift)
      dump_rule(rule, lhs, rules_norm_)
    println()

    println("; definitional rules of normalized functions (these are needed!)")
    for (rule <- rules.defs)
      dump_rule(rule, Nil, Nil)
    println()

    println("fusion rules")
    for (rule <- rules.fuse)
      dump_rule(rule, Nil, Nil)
    println()

    println("; representation rules (they should be immediately inlined)")
    for (rule <- rules.repr)
      dump_rule(rule, Nil, Nil)
    println()

    println("; original definitional rules (should not be used further)")
    for (rule <- rules.flat)
      dump_rule(rule, Nil, Nil)
    println()
  }

  object defs {
    // all original definitions
    var flat: Map[Fun, Def[Flat]] = Map()

    // fused function f.g where g is at f's given positional argument
    var fused: Map[(Fun, Fun, Int), Fun] = Map()

    // functions from flat which have been normalized
    var norm: Map[Fun, Def[Norm]] = Map()
  }

  // equivalences connecting the above functions
  object rules {
    var defs: List[Rule] = Nil
    var flat: List[Rule] = Nil
    var norm: List[Rule] = Nil
    var lift: List[Rule] = Nil
    var fuse: List[Rule] = Nil
    var repr: List[Rule] = Nil
  }

  // discovered lemmas
  var lemmas: List[Rule] = Nil

  val _factor = new Factor(this)
  val _fuse = new Fuse(this)
  val _known = new Known(this)

  def register(df_ : Def[Norm]) {
    val eqs =
      _known.known(df_, defs.norm.values)
    if (eqs.isEmpty) {
      defs.norm += df_.fun -> df_
      rules.defs ++= rules(df_)
    } else {
      rules.repr ++= eqs
    }
  }

  def factor(df: Def[Flat]) {
    val (df_, dfs, eq, eqs) = _factor.factor(df)
    // cuvee.lemmas.Test.show(df_)

    register(df_)
    for (df_ <- dfs)
      register(df_)

    // eq: df => df_
    rules.norm ++= eq
    rules.lift ++= eqs
  }

  def rules(df: Def[CS]) = {
    for (cs <- df.cases)
      yield cs.rule(df.fun)
  }

  def define(df: Def[Flat]) {
    val f = df.fun
    defs.flat += f -> df
    rules.flat ++= rules(df)
  }

  def fuse(df: Def[Flat], dg: Def[Flat]) {
    val stuff = _fuse.fuse(df, dg)
    val (dhs, eqs) = stuff.unzip
    rules.fuse ++= eqs
    for (dh <- dhs) {
      define(dh)
      factor(dh)
    }
  }

  def prove(cmds: List[Cmd]) {
    val goals =
      for (Assert(Not(expr)) <- cmds)
        yield expr

    val rs = rules.fuse ++ rules.repr ++ rules.norm ++ rules.defs
    val rs_ = rs.groupBy(_.fun)
    println("; goals:")
    for (goal <- goals) {
      val goal_ = Rewrite.rewrite(goal, rs_)
      println(goal)
      println(goal_)
    }
    println()
  }

  def seed(cmds: List[Cmd]) {
    val eqs0 =
      for (
        Assert(expr) <- cmds;
        eq <- Def.rw(expr, st)
      )
        yield eq

    val eqs1 =
      for (
        DefineFun(name, formals, res, body, _) <- cmds;
        eq <- Def.rw(name, formals, res, body, st)
      )
        yield eq

    val eqs = eqs0 ++ eqs1

    val dfs =
      for ((fun, stuff) <- eqs.groupBy(_._1))
        yield {
          val (_, cases) = stuff.unzip
          Def(fun, cases)
        }

    for (df <- dfs) {
      define(df)
    }

    // note: perhaps modified in the two loops below
    val flat = defs.flat
    // println("; all defs: " + flat.keySet)

    for ((f, df) <- flat)
      factor(df)

    for ((f, df) <- flat; (g, dg) <- flat)
      fuse(df, dg)
  }
}

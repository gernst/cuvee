package cuvee.lemmas

import java.io.PrintStream
import cuvee.smtlib._
import cuvee.pure._
import cuvee.util.Run
import cuvee.util.Main
import cuvee.State

object isaplanner
    extends Run(
      Test,
      "/home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/isaplanner/prop_83.smt2"
    )

object tip2015_mod_same
    extends Run(
      Test,
      "/home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/tip2015/mod_same.smt2"
    )
object isaplanner_prop52 extends Run(Test, "examples/smtlib/prop_52.smt2")

// object append extends Run(Test, "examples/boogie/append.bpl")

object debug_smt2 extends Run(Test, "debug.smt2")
object poly extends Run(Test, "examples/boogie/poly.bpl")
object assoc extends Run(Test, "examples/boogie/assoc.bpl")
object length extends Run(Test, "examples/boogie/length.bpl")
object layout extends Run(Test, "examples/boogie/layout.bpl")
object sum extends Run(Test, "examples/boogie/sum.bpl")
object length_nat extends Run(Test, "-use:AdtInd", "examples/smtlib/length-nat.smt2")
object length_ extends Run(Test, "-use:AdtInd", "-no:Internal", "examples/smtlib/length.smt2")
object reverse
    extends Run(
      Test,
//  "-use:AdtInd",
      "examples/boogie/reverse.bpl"
    )
// object replace extends Run(Test, "examples/smtlib/replace.smt2")
object contains extends Run(Test, "examples/smtlib/contains_only.smt2")
object tree2 extends Run(Test, "examples/boogie/tree-update.bpl")
object debug extends Run(Test, "examples/boogie/debug.bpl")

object bdd extends Run(Test, "examples/boogie/bdd-test.bpl")

object append extends Run(Test, "examples/lemmas/append.bpl")
object remove extends Run(Test, "-use:shortcut", "examples/lemmas/remove.bpl")
object take_drop extends Run(Test, "examples/lemmas/take_drop.bpl")
object filter extends Run(Test, "-use:shortcut", "examples/lemmas/filter.bpl")

object nat extends Run(Test, "examples/lemmas/nat.bpl")
object list extends Run(Test, "-use:shortcut", "examples/lemmas/list.bpl")
object tree extends Run(Test, "examples/lemmas/tree.bpl")

object Test extends Main {
  var out: PrintStream = null
  var rounds = 3
  var useAdtInd = false
  var useInternal = true
  // cuvee.smtlib.solver.debug = true

  def run(decls: List[DeclareFun], cmds: List[Cmd], defs: List[Def], st: State) = {
    implicit val solver = Solver.z3(100)
    Deaccumulate.neutral = Deaccumulate.defaultNeutral

    for (cmd <- cmds) cmd match {
      case SetLogic(_)      =>
      case _: Lemma         =>
      case Assert(Not(phi)) =>
      case _ =>
        solver.exec(cmd, null)
    }

    val goals =
      for ((Assert(Not(phi))) <- cmds)
        yield phi

    val lemmas = new Lemmas(decls, cmds, defs, st, solver)
    lemmas.useInternal = useInternal
    lemmas.useAdtInd = useAdtInd

    for (
      Lemma(phi, _, _) <- cmds;
      Rule(lhs, rhs, cond, Nil) <- Rules.from(phi, lemmas.original)
    ) {
      lemmas.addLemma("provided", lhs, rhs, cond)
      // lemmas.lemmas = ("provided", eq) :: lemmas.lemmas
    }

    lemmas.findNeutral(defs map (_.fun))

    for (df <- defs) {
      lemmas.define(df)
      lemmas.deaccumulate(df)
      lemmas.recognizeConditional(df)
    }

    for (df <- defs; dg <- defs) {
      lemmas.fuse(df, dg)
    }

    for (i <- 0 until rounds) {
      val before = lemmas.lemmas map (_._2.toExpr) filter (_.funs subsetOf lemmas.original)
      lemmas.round()
      lemmas.cleanup()
      val after = lemmas.lemmas map (_._2.toExpr) filter (_.funs subsetOf lemmas.original)
      println("--------")
      lemmas.show()

      import cuvee.util.TheoryComparison
      println("merit of this round: ")
      println(after)
      println(before)
      println(before % after)
      println("--------")

      lemmas.next()
    }

    solver.ack(Exit)
    solver.destroy()

    lemmas.lemmas
  }

  def main(args: Array[String]) {
    Rules.ite = true
    Rules.shortcut = false
    val files = configure(args.toList)

    if (out == null)
      out = log("log.txt")

    for (file <- files) {
      try {
        val (cmds, st) = read(file)
        val (decls, defs) = prepare(cmds, st)
        println(file)
        run(decls, cmds, defs, st)
      } catch {
        case e: cuvee.smtlib.Error =>
          println(e.info)
        case e: Exception =>
          e.printStackTrace()
          println(e)
      }
    }
  }

  def configure(args: List[String]): List[String] = args match {
    case Nil =>
      Nil

    case "-rounds" :: arg :: rest =>
      rounds = arg.toInt
      configure(rest)

    case "-use:AdtInd" :: rest =>
      useAdtInd = true
      configure(rest)

    case "-use:shortcut" :: rest =>
      Rules.shortcut = true
      configure(rest)

    case "-no:Internal" :: rest =>
      useInternal = false
      configure(rest)

    case "-out" :: file :: rest =>
      out = log(file)
      configure(rest)

    case first :: rest =>
      first :: configure(rest)
  }
}

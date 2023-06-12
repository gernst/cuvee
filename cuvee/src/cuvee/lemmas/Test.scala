package cuvee.lemmas

import java.io.PrintStream
import cuvee.smtlib._
import cuvee.pure._
import cuvee.util.Run
import cuvee.util.Main

object isaplanner1
    extends Run(
      Test,
      "/home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/isaplanner/prop_01.smt2"
    )

object append extends Run(Test, "-rounds", "1", "examples/boogie/append.bpl")

object debug_smt2 extends Run(Test, "debug.smt2")
object poly extends Run(Test, "examples/boogie/poly.bpl")
object assoc extends Run(Test, "examples/boogie/assoc.bpl")
object length extends Run(Test, "examples/boogie/length.bpl")
object nat extends Run(Test, "examples/boogie/nat.bpl")
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
object list extends Run(Test, "examples/smtlib/list-defs.smt2")
object remove extends Run(Test, "examples/smtlib/remove.smt2")
object tree extends Run(Test, "examples/boogie/tree.bpl")
object tree2 extends Run(Test, "examples/boogie/tree-update.bpl")
object debug extends Run(Test, "debug.bpl")

object bdd extends Run(Test, "examples/boogie/bdd-test.bpl")

object Test extends Main {
  var out: PrintStream = null
  var rounds = 3
  var useAdtInd = false
  var useInternal = true
  // cuvee.smtlib.solver.debug = true

  def main(args: Array[String]) {
    val files = configure(args.toList)

    if (out == null)
      out = log("log.txt")

    Rules.shortcut = false

    for (file <- files) {
      try {
        val (decls, defs, cmds, st) = read(file)
        println(file)

        val solver = cuvee.smtlib.z3(st, 100)

        for (cmd <- cmds) cmd match {
          case SetLogic(_) =>
          case Lemma(_, _) =>
          case _ =>
            solver.exec(cmd)
        }

        val goals =
          for ((Assert(Not(phi))) <- cmds)
            yield phi

        val lemmas = new Lemmas(decls, cmds, defs, st, solver)
        lemmas.useInternal = useInternal
        lemmas.useAdtInd = useAdtInd

        for (
          Lemma(phi, _) <- cmds;
          Rule(lhs, rhs, cond, Nil) <- Rules.from(phi, lemmas.original)
        ) {
          lemmas.addLemma("provided", lhs, rhs, cond)
          // lemmas.lemmas = ("provided", eq) :: lemmas.lemmas
        }

        for (df <- defs) {
          lemmas.define(df)
          lemmas.deaccumulate(df)
        }

        for (df <- defs; dg <- defs) {
          lemmas.fuse(df, dg)
        }

        for (i <- 0 until rounds) {
          lemmas.round()
          lemmas.cleanup()
          println("--------")
          lemmas.show()
          println("--------")

          lemmas.next()
        }

        solver.exec(Exit)
        solver.destroy()
      } catch {
        case e: cuvee.smtlib.Error =>
          println(e.info)
        case e: Exception =>
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

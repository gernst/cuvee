package cuvee

import cuvee.pipe._
import cuvee.util.Printer
import cuvee.smtlib.Solver
import cuvee.prove.Prove
import cuvee.prove.SimpleProver
import cuvee.prove.Prover
import cuvee.lemmas.Lemmas
import cuvee.imp.Eval
import cuvee.imp.Annotate
import cuvee.prove.PositiveProver
import cuvee.lemmas.Enumerate
import cuvee.lemmas.recognize.Neutral
import cuvee.prove.QuickCheck
import cuvee.smtlib.Lemma
import cuvee.pure.Rewrite

class Config {
  var file: Option[String] = None
  var printer: Printer = smtlib.printer

  var source: Source = smtlib.source()
  var sink: (Printer => Sink) = Sink.stdout(_)
  var report: (Printer => Report) = Report.stderr(_)

  var eval = false
  var annotate = false
  var lemmas = "none"
  var lemmasRounds = 3
  var conditionalLemmas = false
  var lemmasWithSyntheticFunctions = false

  var simplify = false
  var rewrite = false

  var prove = "none"
  var induct = false
  var quickcheck = true

  var proveNegatedAsserts = true
  var crosscheckProver = false

  def option(name: String, help: String)(action: => Unit) = {
    name -> (help, () => action)
  }

  def help() {
    println("./Cuvee.sh [options] <file>")

    for ((flag, (description, _)) <- options) {
      println("  " + flag)
      println("      " + description)
      println()
    }

    System.exit(0)
  }

  val options = Map(
    option("-help", "show this help text") { help() },
    option("-log:info", "print some informative output to stderr, such as progress") {
      printer = cuvee.smtlib.printer
    },
    option("-log:debug", "print lots of internals to stderr, includes -log:info") {
      printer = cuvee.smtlib.printer
    },
    option("-debug:solver", "show interaction SMT-LIB backends") {
      Solver.debug = true
    },
    option("-z3", "process final output via Z3") {
      sink = _ => Solver.z3()
      report = Report.stdout(_)
    },
    option("-prove:quickcheck", "quick check lemmas for counterexamples (default)") {
      quickcheck = true
    },
    option("-prove:no-quickcheck", "quick check lemmas for counterexamples") {
      quickcheck = false
    },
    option("-print:smtlib", "force output to SMT-LIB format") {
      printer = cuvee.smtlib.printer
    },
    option("-print:boogie", "force output to Boogie format") {
      printer = cuvee.boogie.printer
    },
    option("-print:thesy", "force output to TheSy format") {
      printer = cuvee.thesy.printer
    },
    // option("-print:none", "suppress output") {
    //   printer = Printer.dummy
    // },
    option("-prove:auto", "prove lemmas with tactics and structural simplification using Z3") {
      prove = "auto"
    },
    option("-prove:z3", "prove lemmas with tactics and Z3 as endgame solver") {
      prove = "z3"
    },
    option("-prove:dump", "dump lemmas to prove into file") {
      prove = "dump"
    },
    option(
      "-prove:crosscheck",
      "cross-check simplifications of prover by Z3 (may fail due to incompleteness)"
    ) {
      crosscheckProver = true
    },
    option("-prove:dummy", "just apply tactics to lemmas") {
      prove = "dummy"
    },
    option("-lemmas:neutral", "infer lemmas by guessing neutral laws") {
      lemmas = "neutral"
    },
    option("-lemmas:structural", "infer lemmas by structural methods") {
      lemmas = "structural"
    },
    option(
      "-lemmas:structural+conditional",
      "infer lemmas by structural methods, including conditional ones"
    ) {
      lemmas = "structural"
      conditionalLemmas = true
    },
    option("-lemmas:enumerate", "infer lemmas with term enumeration") {
      lemmas = "enumerate"
    },
    option(
      "-lemmas:all",
      "include lemmas that are formulated over synthetic functions (structural methods)"
    ) {
      lemmasWithSyntheticFunctions = true
    },
    option("-simplify", "simplify using internal algorithms") {
      simplify = true
    },
    option(
      "-simplify+rewrite",
      "simplify with additional rewrite rules inferred from axioms and definitions"
    ) {
      simplify = true
      rewrite = true
    },
    option("-eval", "evaluate correctness of programs to expressions") {
      eval = true
    },
    option("-annotate", "infer loop annotations") {
      annotate = true
    },
    option("-prove:induct", "prove by trying automatic induction") {
      induct = true
    }
  )

  def configure(args: List[String]): Unit = args match {
    case Nil =>

    case first :: rest if options contains first =>
      val (_, action) = options(first)
      action()
      configure(rest)

    case "-lemmas:rounds" :: arg :: rest =>
      lemmasRounds = arg.toInt
      configure(rest)

    case "-o" :: path :: rest =>
      sink = Sink.file(path)(_)
      report = Report.stdout(_)

      if (path endsWith ".bpl")
        printer = cuvee.boogie.printer
      else if (path endsWith ".smt2")
        printer = cuvee.smtlib.printer
      else if (path endsWith ".th")
        printer = cuvee.thesy.printer

      configure(rest)

    case first :: rest if first startsWith "-" =>
      error("not an option: " + first)

    case path :: rest =>
      require(file.isEmpty, "only a single file is allowed, already given: " + file.get)
      file = Some(path)

      if (path endsWith ".bpl") {
        printer = boogie.printer
        source = boogie.source(path)
      } else if (path endsWith ".smt2") {
        printer = smtlib.printer
        source = smtlib.source(path)
      } else if (path endsWith ".py") {
        source = python.source(path)
      } else if (path endsWith ".th") {
        printer = thesy.printer
        source = thesy.source(path)
      } else {
        error("unknown file format: " + path)
      }

      configure(rest)
  }
}

object Config {
  def apply(args: Array[String]) = {
    val config = new Config()
    config.configure(args.toList)
    val file = config.file
    val source = config.source

    var sink: Sink = null
    sink = config.sink(config.printer)

    config.prove match {
      case "auto" =>
        val solver = Solver.z3()
        val prover = new PositiveProver(solver)
        if (config.induct)
          error("induction not supported by auto prover")
        sink = new Incremental(
          new Prove(
            prover,
            config.simplify,
            config.rewrite,
            config.proveNegatedAsserts,
            config.crosscheckProver
          ),
          sink
        )

      case "z3" =>
        val solver = Solver.z3()
        val prover = Prover.fromSolver(solver, config.induct)
        sink = new Incremental(
          new Prove(
            prover,
            config.simplify,
            config.rewrite,
            config.proveNegatedAsserts,
            config.crosscheckProver
          ),
          sink
        )

      case "dummy" =>
        val solver = Solver.dummy
        val prover = Prover.fromSolver(solver, config.induct)
        sink = new Incremental(
          new Prove(
            prover,
            config.simplify,
            config.rewrite,
            config.proveNegatedAsserts,
            config.crosscheckProver
          ),
          sink
        )

      case "dump" =>
        val prover = Prover.dump("./lemma")
        sink = new Incremental(
          new Prove(
            prover,
            config.simplify,
            config.rewrite,
            config.proveNegatedAsserts,
            config.crosscheckProver
          ),
          sink
        )

      case _ =>
    }

    if (config.quickcheck) {
      sink = new Incremental(QuickCheck, sink)
    }

    if (config.lemmas == "structural") {
      sink = new Incremental(
        new Lemmas(
          config.lemmasRounds,
          config.conditionalLemmas,
          config.lemmasWithSyntheticFunctions
        ),
        sink
      )
    }

    if (config.lemmas == "enumerate") {
      sink = new Incremental(new Enumerate(config.lemmasRounds), sink)
    }

    if (config.lemmas == "neutral") {
      sink = new Incremental(Neutral, sink)
    }

    if (config.eval) {
      sink = new Incremental(Eval, sink)
    }

    if (config.annotate) {
      sink = new Incremental(Annotate, sink)
    }

    // println("pipeline: " + sink)

    val report = config.report(config.printer)
    (file, source, sink, report)
  }
}

object Cuvee {
  def main(args: Array[String]) {
    val (file, source, sink, report) = Config(args)
    Pipe.run(source, sink, report)
  }
}

object CompareTheories {
  var mode = "paper"

  def configure(args: List[String]): List[String] = args match {
    case "-full" :: rest =>
      mode = "full"
      configure(rest)

    case "-nontrivial" :: rest =>
      mode = "nontrivial"
      configure(rest)

    case "-reduced" :: rest =>
      mode = "reduced"
      configure(rest)

    case _ =>
      args
  }

  def main(args: Array[String]) = {
    require(
      args.length >= 2,
      "Usage: ./CompareTheories.sh <definitions> <baseline> <comparison1> <comparison2> ..."
    )
    val Array(theory, baseline, rest @ _*) = args

    try {
      val (cmds, st) = parse(theory)

      implicit val solver = Solver.z3(100)
      // Solver.debug = true

      for (cmd <- cmds)
        solver.ack(cmd)

      val rws = Rewrite.from(cmds, st)
      val qc = new QuickCheck(rws.groupBy(_.fun), st)

      def lemmasOf(file: String) = if (file endsWith ".th.log") {
        cuvee.thesy.storedLemmas(file, st)
      } else {
        val (cmds, _) = parse(file)
        cmds collect { case Lemma(phi, _, _) => phi }
      }

      import util.TheoryComparison

      val self = lemmasOf(baseline)

      val wrong = self filter { phi =>
        qc.hasSimpleCounterexample(phi, depth = 2)
      }

      mode match {
        case "informative" =>
          println(baseline)
          println("  " + self.length + "  number of lemmas")
          println("  " + wrong.length + "  wrong (counterexample by testing)")
          println("  " + self.countNontrivial + "  nontrivial")
          println("  " + self.reduced.length + "  reduced")

          for (file <- rest) {
            val other = lemmasOf(file)
            println("  " + self.advantageOver(other) + "  " + file)
          }

        case "paper" =>


      }
    } catch {
      case e @ smtlib.Error(msg) =>
        println(msg)
      case e: Exception =>
        e.printStackTrace()
    }
  }

}

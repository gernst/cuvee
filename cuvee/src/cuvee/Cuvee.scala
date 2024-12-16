package cuvee

import cuvee.pipe._
import cuvee.util.Printer
import cuvee.smtlib.Solver
import cuvee.prove.Prove
import cuvee.prove.SimpleProver
import cuvee.prove.Prover
import cuvee.lemmas.Lemmas
import cuvee.imp.VCGenStage
import cuvee.imp.Annotate
import cuvee.prove.PositiveProver
import cuvee.lemmas.Enumerate
import cuvee.lemmas.recognize.Neutral
import cuvee.prove.QuickCheck
import cuvee.smtlib.Lemma
import cuvee.pure.Rewrite
import cuvee.ai.Abstract
import cuvee.pure.Horn
import cuvee.imp.annotate
import cuvee.util.Main
import cuvee.pure.Expr
import cuvee.smtlib.{Cmd, Res}
import cuvee.smtlib.Success

class Config {
  var file: Option[String] = None
  var printer: Printer = smtlib.printer
  var overridePrinter = false

  var source: Source = smtlib.source()
  var sink: (Printer => Sink) = Sink.stdout(_)
  var report: (Printer => Report) = Report.stderr(_)

  var vcgen = false
  var vcgen_partial = false

  var lemmas = "none"
  var lemmasRounds = 3
  var conditionalLemmas = false
  var lemmasWithSyntheticFunctions = false

  var annotate: Set[String] = Set()

  var simplify = false
  var rewrite = false

  var prove = "none"
  var induct = false
  var quickcheck = true
  var split = false

  var useContractlib = false

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

  def version() {
    println(cuvee.version)
    System.exit(0)
  }

  val options = Map(
    option("-help", "show this help text") {
      help()
    },
    option("-version", "print version number") {
      version()
    },
    // option(
    //   "-log:info",
    //   "print some informative output to stderr, such as progress"
    // ) {
    //   printer = cuvee.smtlib.printer
    // },
    // option(
    //   "-log:debug",
    //   "print lots of internals to stderr, includes -log:info"
    // ) {
    //   printer = cuvee.smtlib.printer
    // },
    option("-debug:solver", "show interaction SMT-LIB backends") {
      Solver.debug = true
    },
    option("-prove:strict", "throw an exception if goals are left") {
      Solver.fail = true
    },
    option("-z3", "process final output via Z3") {
      sink = _ => Solver.z3()
      report = Report.stdout(_)
    },
    option(
      "-prove:quickcheck",
      "quick check lemmas for counterexamples (default)"
    ) {
      quickcheck = true
    },
    option(
      "-prove:no-quickcheck",
      "do not make a quick check for counterexamples for lemmas"
    ) {
      quickcheck = false
    },
    option("-print:smtlib", "force output to SMT-LIB format") {
      printer = cuvee.smtlib.printer
      overridePrinter = true
    },
    option("-print:boogie", "force output to Boogie format") {
      printer = cuvee.boogie.printer
      overridePrinter = true
    },
    option("-print:thesy", "force output to TheSy format") {
      printer = cuvee.thesy.printer
      overridePrinter = true
    },
    option("-parse:contractlib", "make Contract-LIB theories available") {
      useContractlib = true
    },
    // option("-print:none", "suppress output") {
    //   printer = Printer.dummy
    // },
    option(
      "-prove:auto",
      "prove lemmas with tactics and structural simplification using Z3"
    ) {
      prove = "auto"
    },
    option("-prove:z3", "prove lemmas with tactics and Z3 as endgame solver") {
      prove = "z3"
    },
    option("-prove:cvc5", "prove lemmas with tactics and CVC5 as endgame solver") {
      prove = "cvc5"
    },
    option("-prove:simplify", "use the internal simplifier to reduce lemmas") {
      prove = "simplify"
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
    option("-prove:simple", "simple recursive prover") {
      prove = "simple"
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
    option(
      "-vcgen",
      "generate verification conditions for procedures and wp operators"
    ) {
      vcgen = true
    },
    option(
      "-vcgen:partial",
      "generate verification conditions without termination"
    ) {
      vcgen = true
      vcgen_partial = true
    },
    option("-eval", "obsolete flag, may change meaning in the future") {
      cuvee.error("the -eval flag has been superseded by the -vcgen flag")
    },
    option(
      "-annotate:polyhedra",
      "infer loop annotations (polyhedra abstract domain)"
    ) {
      annotate += "polyhedra"
    },
    option("-annotate:new-arrays", "infer loop annotations (array acceleration)") {
      annotate += "new-arrays"
    },
    option("-annotate:arrays", "infer loop annotations (array acceleration)") {
      annotate += "arrays"
    },
    option(
      "-annotate:arrays+frame",
      "infer loop annotations (array acceleration)"
    ) {
      annotate ++= Set("arrays", "frame")
    },
    option(
      "-annotate:arrays+guard",
      "infer loop annotations (array acceleration)"
    ) {
      annotate ++= Set("arrays", "guard")
    },
    option(
      "-annotate:arrays+frame+guard",
      "infer loop annotations (array acceleration)"
    ) {
      annotate ++= Set("arrays", "frame", "guard")
    },
    option("-prove:induct", "prove by trying automatic induction") {
      induct = true
    },
    option("-split", "split VCs as Horn clauses") {
      split = true
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

    case "-o" :: path :: rest if path endsWith ".java" =>
      sink = cuvee.util.JavaBenchmarkWriter.sink(path)
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
      require(
        file.isEmpty,
        "only a single file is allowed, already given: " + file.get
      )
      file = Some(path)

      if (path endsWith ".bpl") {
        if (!overridePrinter) printer = boogie.printer
        source = boogie.source(path)
      } else if (path endsWith ".smt2") {
        if (!overridePrinter) printer = smtlib.printer
        source = smtlib.source(path)
      } else if (path endsWith ".py") {
        source = python.source(path)
      } else if (path endsWith ".c") {
        printer = boogie.printer
        source = c.source(path)
      } else if (path endsWith ".yml") {
        printer = boogie.printer
        source = c.yml.source(path)
      } else if (path endsWith ".th") {
        if (!overridePrinter) printer = thesy.printer
        source = thesy.source(path)
      } else {
        error("unknown file format: " + path)
      }

      if (useContractlib)
        source.state.withContractLib

      configure(rest)
  }
}

object Config {
  def apply(args: Array[String], secondary: Array[Sink] = Array()) = {
    val config = new Config()
    config.configure(args.toList)
    val file = config.file
    val source = config.source

    var sink: Sink = null
    sink = config.sink(config.printer)

    if (secondary.nonEmpty)
      sink = new Sink.tee(sink, secondary: _*)

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

      case "simple" =>
        val solver = Solver.z3()
        val prover = new SimpleProver(solver)
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

      case "cvc5" =>
        val solver = Solver.cvc5()
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

      case "simplify" =>
        val solver = Solver.z3()
        val prover = Prover.fromSimplifier
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
        // val solver = Solver.dummy
        val prover = Prover.dummy // fromSolver(solver, config.induct)
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
      sink = new Incremental(
        new Enumerate(config.lemmasRounds, config.lemmasWithSyntheticFunctions),
        sink
      )
    }

    if (config.lemmas == "neutral") {
      sink = new Incremental(Neutral, sink)
    }

    if (config.split) {
      sink = new Incremental(Horn, sink)
    }

    if (config.vcgen) {
      sink = new Incremental(new VCGenStage(config.vcgen_partial), sink)
    }

    if (config.annotate contains "polyhedra") {
      sink = new Incremental(Abstract, sink)
    }

    if (config.annotate contains "new-arrays") {
      sink = new Incremental(annotate.NewArrays, sink)
    }

    if (config.annotate contains "arrays") {
      sink = new Incremental(
        annotate.Arrays(
          config.annotate contains "frame",
          config.annotate contains "guard"
        ),
        sink
      )
    }

    // println("pipeline: " + sink)

    val report = config.report(config.printer)
    (file, source, sink, report)
  }
}

object Cuvee extends Main {
  def main(args: Array[String]) {
    Expr.resetIndex()
    val (file, source, sink, report) = Config(args)
    Pipe.run(source, sink, report)
  }

  def collect(args: Array[String]) = {
    Expr.resetIndex()

    val capture = new Sink.capture
    val (file, source, sink, report) = Config(args, Array(capture))
    Pipe.run(source, sink, report)

    capture.rcmds.reverse
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
        cmds collect { case Lemma(phi, _, _, _) => phi }
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

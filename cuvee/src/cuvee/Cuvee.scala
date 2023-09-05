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

class Config {
  var file: Option[String] = None
  var printer: Printer = smtlib.printer

  var source: Source = smtlib.source()
  var sink: (Printer => Sink) = Sink.stdout(_)
  var report: (Printer => Report) = Report.stderr(_)

  var eval = false
  var annotate = false
  var lemmas = false

  var simplify = false
  var rewrite = false

  var prove = "none"
  var induct = false

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
    option("-debug:solver", "show interaction SMT-LIB backends") {
      Solver.debug = true
    },
    option("-z3", "process final output via Z3") {
      sink = _ => Solver.z3()
      report = Report.stdout(_)
    },
    option("-print:smtlib", "force output to SMT-LIB format") {
      printer = cuvee.smtlib.printer
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
    option("-prove:dummy", "just apply tactics to lemmas") {
      prove = "dummy"
    },
    option("-lemmas", "infer lemmas") {
      lemmas = true
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
        sink = new Incremental(new Prove(prover, config.simplify, config.rewrite), sink)

      case "z3" =>
        val solver = Solver.z3()
        val prover = Prover.fromSolver(solver, config.induct)
        sink = new Incremental(new Prove(prover, config.simplify, config.rewrite), sink)

      case "dummy" =>
        val solver = Solver.dummy
        val prover = Prover.fromSolver(solver, config.induct)
        sink = new Incremental(new Prove(prover, config.simplify, config.rewrite), sink)

      case "dump" =>
        val prover = Prover.dump("./lemma")
        sink = new Incremental(new Prove(prover, config.simplify, config.rewrite), sink)

      case _ =>
    }

    if (config.lemmas) {
      sink = new Incremental(Lemmas, sink)
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

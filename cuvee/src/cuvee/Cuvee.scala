package cuvee

import cuvee.pipe._
import cuvee.util.Printer
import cuvee.smtlib.Solver
import cuvee.prove.Prove
import cuvee.prove.SimpleProver
import cuvee.prove.Prover

class Config {
  var file: Option[String] = None
  var printer: Printer = smtlib.printer

  var source: Source = smtlib.source()
  var sink: (Printer => Sink) = Sink.stdout(_)
  var report: (Printer => Report) = Report.stderr(_)

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
    }
  )

  def configure(args: List[String]): Unit = args match {
    case Nil =>

    case first :: rest if options contains first =>
      val (_, action) = options(first)
      action()
      configure(rest)

    case path :: rest =>
      require(file.isEmpty, "only a single file is allowed, already given: " + file.get)
      file = Some(path)

      if (path endsWith ".bpl") {
        printer = boogie.printer
        source = boogie.source(path)
      } else if (path endsWith ".smt2") {
        printer = smtlib.printer
        source = smtlib.source(path)
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

    val solver = Solver.z3()
    val prover = Prover.fromSolver(solver)
    sink = new Incremental(new Prove(prover), sink)

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

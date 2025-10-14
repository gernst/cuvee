package cuvee.pipe

import cuvee.smtlib._
import java.io.PrintStream
import cuvee.util.Printer

trait Report {
  var printSuccess: Boolean
  var incremental: Boolean

  def report(f: => Res)

  def apply(f: => Res) = safe {
    report(f)
  }

  def safe[A](f: => A): Option[A] = try {
    Some(f)
  } catch {
    case e: cuvee.smtlib.Error =>
      report(e)
      if (!incremental)
        cuvee.abort()
      else
        None

    // Escalate internal errors to terminal for now
    // case e: Exception if !Solver.fail =>
    //   // report(new Error(List("internal error", e.getMessage())))
    //   e.printStackTrace()
  }
}

object Report {
  def stdout(printer: Printer) = new print(System.out, printer)
  def stderr(printer: Printer) = new print(System.err,printer)

  class print(stream: PrintStream, printer: Printer) extends Report {
    var printSuccess = false
    var incremental = false

    def report(f: => Res) = f match {
      case ack: Ack if !printSuccess =>
      // suppressed response

      case res =>
        for (line <- printer.lines(res))
          stream.println(line)
    }
  }
}

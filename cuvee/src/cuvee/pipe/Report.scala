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

  def safe[A](f: => A) = try {
    f
  } catch {
    case e: cuvee.smtlib.Error =>
      report(e)
      if (!incremental)
        cuvee.abort()

    // Escalate internal errors to terminal for now
    // case e: Exception if !Solver.fail =>
    //   // report(new Error(List("internal error", e.getMessage())))
    //   e.printStackTrace()
  }
}

object Report {
  def stdout(implicit printer: Printer) = new print(System.out)
  def stderr(implicit printer: Printer) = new print(System.err)

  class print(stream: PrintStream)(implicit printer: Printer) extends Report {
    var printSuccess = false
    var incremental = false

    def report(f: => Res) = f match {
      case ack: Ack if !printSuccess =>
      // suppressed response

      case res =>
        for (line <- res.lines)
          stream.println(line)
    }
  }
}

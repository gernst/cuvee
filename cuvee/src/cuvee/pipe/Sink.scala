package cuvee.pipe

import cuvee.util.Name

import cuvee.pure._
import cuvee.smtlib._
import cuvee.imp._
import cuvee.util.Tool
import java.io.PrintStream
import cuvee.util.Printer
import cuvee.State

trait Sink {
  // avoid external calls
  protected def exec(cmd: Cmd, state: State): Res

  // this is the interface to use by clients
  def apply(cmd: Cmd, state: State): Res = {
    exec(cmd, state)
  }
}

object Sink {
  def stdout(implicit printer: Printer) = new print(System.out)
  def stderr(implicit printer: Printer) = new print(System.err)

  class print(stream: PrintStream)(implicit printer: Printer) extends Sink {
    def exec(cmd: Cmd, state: State): Res = {
      for (line <- cmd.lines)
        stream.println(line)

      cmd match {
        case CheckSat => Unknown
        case GetModel => cuvee.error("no model available")
        case _        => Success
      }
    }
  }

  class tee(primary: Sink, secondary: Sink*) extends Sink {
    def exec(cmd: Cmd, state: State) = {
      for (that <- secondary)
        that.exec(cmd, state)
      primary.exec(cmd, state)
    }
  }
}

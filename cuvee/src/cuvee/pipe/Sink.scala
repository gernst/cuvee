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
  def exec(cmd: Cmd, state: State): Res
  def done(state: State)
}

object Sink {
  def stdout(implicit printer: Printer) = new print(System.out)
  def stderr(implicit printer: Printer) = new print(System.err)

  class print(stream: PrintStream)(implicit printer: Printer) extends Sink {
    def done(state: State) {}

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
    def done(state: State) = {
      for (that <- secondary)
        that.done(state)
      primary.done(state)
    }

    def exec(cmd: Cmd, state: State) = {
      for (that <- secondary)
        that.exec(cmd, state)
      primary.exec(cmd, state)
    }
  }
}

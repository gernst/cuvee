package cuvee.pipe

import cuvee.util.Name

import cuvee.pure._
import cuvee.smtlib._
import cuvee.imp._
import cuvee.backend.Tactic
import cuvee.util.Tool
import java.io.PrintStream
import cuvee.util.Printer
import cuvee.State

trait Sink {
  def exec(cmd: Cmd): Res
}

object Sink {
  def stdout(implicit printer: Printer) = new print(System.out)
  def stderr(implicit printer: Printer) = new print(System.err)

  class print(stream: PrintStream)(implicit printer: Printer) extends Sink {
    def exec(cmd: Cmd): Res = {
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
    def exec(cmd: Cmd) = {
      for (that <- secondary)
        that.exec(cmd)
      primary.exec(cmd)
    }
  }
}

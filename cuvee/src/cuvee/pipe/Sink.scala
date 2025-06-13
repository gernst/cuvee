package cuvee.pipe

import cuvee.util.Name

import cuvee.pure._
import cuvee.smtlib._
import cuvee.imp._
import cuvee.util.Tool
import java.io.PrintStream
import cuvee.util.Printer
import cuvee.State
import java.io.FileOutputStream

trait Sink {
  def init(state: State) {}
  def done(state: State) {}
  def exec(cmd: Cmd, state: State): Res

  def exec(cmds: List[Cmd], state: State): List[Res] = {
    for (cmd <- cmds)
      yield exec(cmd, state)
  }
}

object Sink {
  object dummy extends Sink {
    def exec(cmd: Cmd, state: State) = cmd match {
      case CheckSat =>
        Unknown
      case _ =>
        Success
    }
  }

  def stdout(implicit printer: Printer) =
    new print(System.out)

  def stderr(implicit printer: Printer) =
    new print(System.err)

  def file(name: String)(implicit printer: Printer) =
    new print(new PrintStream(new FileOutputStream(name)))

  class capture extends Sink {
    var rcmds: List[Cmd] = Nil

    override def exec(cmd: Cmd, state: State): Res = {
      rcmds = cmd :: rcmds
      Success
    }
  }

  class print(stream: PrintStream)(implicit printer: Printer) extends Sink {
    var status: Res = Unknown

    def exec(cmd: Cmd, state: State): Res = {
      for (line <- cmd.lines)
        stream.println(line)

      cmd match {
        // make sure we report unsat for lemmas proved by Prove
        case Assert(False) => status = Unsat; Success
        case Pop(_)        => status = Unknown; Success
        case CheckSat      => status
        case GetModel      => Error("no model available")
        case Labels        => Error("no labels available")
        case _             => Success
      }
    }
  }

  class tee(primary: Sink, secondary: Sink*) extends Sink {
    override def init(state: State) = {
      for (that <- secondary)
        that.init(state)
      primary.init(state)
    }

    override def done(state: State) = {
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

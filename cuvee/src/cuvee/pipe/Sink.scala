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
  // avoid external calls
  protected def exec(cmd: Cmd): Res

  // this is the interface to use by clients
  def apply(cmd: Cmd): Res = {
    exec(cmd)
  }
}

trait Stateful {
  this: Sink =>

  class Entry(var rcmds: List[Cmd], val state: State) {
    def copy() = {
      new Entry(rcmds, state.copy())
    }

    def add(cmd: Cmd) {
      state.add(cmd)
      rcmds = cmd :: rcmds
    }
  }

  var stack = List(new Entry(Nil, State.default))

  def top = stack.head
  def state = top.state
  def cmds = top.rcmds.reverse

  def exec(cmd: Cmd): Res

  override def apply(cmd: Cmd): Res = {
    cmd match {
      case Push(n) =>
        val add = List.tabulate(n) { _ => top.copy() }
        stack = add ++ stack
        exec(cmd)

      case Pop(n) =>
        stack = stack drop n
        exec(cmd)

      case _ =>
        top.add(cmd)
        exec(cmd)
    }
  }
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

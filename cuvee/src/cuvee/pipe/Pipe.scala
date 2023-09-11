package cuvee.pipe

import cuvee.util.Printer
import cuvee.smtlib._
import cuvee.State
import cuvee.sexpr.Id

object Pipe {
  var debug = true
  var printSuccess = false

  def run(source: Source, sink: Sink, report: Report) {
    source foreach {
      case SetOption("print-success", Id("true")) =>
        report.printSuccess = true
      case SetOption("print-success", Id("false")) =>
        report.printSuccess = false
      case cmd =>
        report {
          sink.exec(cmd, source.state)
        }
    }

    sink.done(source.state)
  }
}

// A stage represents a transformation that replaces a sequence of commands
// with another sequence at specific points.
// At such points, we commit to a prefix of the file being fixed.
// A stage therefore receives those commands since the last commit points.
// Stages can be stateful and don't need to worry about push/pop,
// as long as copy produces an independent copy.

trait Stage {
  // executed with every check-sat command (but not lemmas, they just return success or not)
  def exec(prefix: List[Cmd], cmds: List[Cmd], in: State, last: Cmd): List[Cmd]
}

class Incremental(stage: Stage, sink: Sink) extends Sink {
  override def toString = "incremental " + stage + " -> " + sink

  class Entry(var prefix: List[Cmd], var pending: List[Cmd], val state: State) {
    def copy() = new Entry(prefix, pending, state.copy())
  }

  var stack = List(new Entry(Nil, Nil, State.default))
  def top = stack.head

  def done(state: State) {
    flush(state, Exit)
    sink.done(top.state)
  }

  def flush(in: State, last: Cmd) {
    val add = top.pending.reverse
    val cmds = stage.exec(top.prefix, add, in, last)

    top.prefix = top.prefix ++ add
    top.pending = Nil

    top.state add cmds
    sink.exec(cmds, top.state)
  }

  def exec(cmd: Cmd, in: State) = cmd match {
    case Push(n) =>
      flush(in, cmd)

      val add = List.tabulate(n) { _ => stack.head.copy }
      stack = add ++ stack
      sink.exec(cmd, top.state)

    case Pop(n) =>
      flush(in, cmd)

      stack = stack drop n
      sink.exec(cmd, top.state)

    // check-sat flushes, lemmas don't
    case CheckSat =>
      flush(in, cmd)
      sink.exec(cmd, top.state)

    // assume here that the model and labels are provided always by the backend,
    // perhaps we can find some more flexible option in the future.
    case Labels | GetModel | _: GetInfo =>
      sink.exec(cmd, top.state)

    case _ =>
      top.pending = cmd :: top.pending
      Success
  }
}

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
  // need to override for stateful components
  def copy(): Stage = this

  // executed with every check-sat command (but not lemmas, they just return success or not)
  def exec(prefix: List[Cmd], cmds: List[Cmd], in: State): List[Cmd]
}

class Incremental(stage: Stage, sink: Sink, flushDone: Boolean = true) extends Sink {
  override def toString = "incremental " + stage + " -> " + sink

  class Entry(var prefix: List[Cmd], val stage: Stage, val state: State) {
    def copy() = new Entry(prefix, stage.copy(), out.copy())
  }

  var stack = List(new Entry(Nil, stage, State.default))
  def top = stack.head
  def out = top.state

  var pending: List[Cmd] = Nil

  def done(state: State) {
    if (flushDone) {
      flush(state)
      sink.done(out)
    }
  }

  def flush(in: State) {
    val cmds = stage.exec(top.prefix, pending.reverse, in)
    out add cmds

    for (cmd <- cmds) {
      sink.exec(cmd, out)
    }

    pending = Nil
  }

  def exec(cmd: Cmd, in: State) = cmd match {
    case Push(n) =>
      val add = List.tabulate(n) { _ => stack.head.copy }
      stack = add ++ stack
      pending = cmd :: pending
      Success
    // sink.exec(cmd, out)

    case Pop(n) =>
      stack = stack drop n
      pending = cmd :: pending
      Success
    // sink.exec(cmd, out)

    // check-sat flushes, lemmas don't
    case CheckSat =>
      flush(in)
      sink.exec(cmd, out)

    case GetModel =>
      // assume here that the model is provided always by the backend,
      // perhaps we can find some more flexible option in the future.
      sink.exec(cmd, out)

    case _ =>
      pending = cmd :: pending
      Success
  }
}

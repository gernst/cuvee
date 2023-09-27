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

    report.safe {
      sink.done(source.state)
    }
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
  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, in: State): List[Cmd]
}

class Incremental(stage: Stage, sink: Sink) extends Sink {
  override def toString = "incremental " + stage + " -> " + sink

  class Entry(var prefix: List[Cmd], val state: State) {
    def copy() = new Entry(prefix, state.copy())
  }

  var pending: List[Cmd] = Nil

  def reset = List(new Entry(Nil, State.default))
  var stack = reset
  def top = stack.head

  def done(state: State) {
    flush(Exit, state)
    sink.done(top.state)
  }

  var added: Set[AnyRef] = Set()

  def flush(last: Cmd, in: State) {
    val add = pending.reverse
    // println("flush")
    // println("  prefix: " + top.prefix)
    // println("  add:    " + add)

    val cmds = stage.exec(top.prefix, add, last, in)
    // println("  cmds:   " + cmds)

    top.prefix = top.prefix ++ add
    val distinct = top.prefix.distinct

    if (distinct != top.prefix) {
      // println(distinct)
      // println(top.prefix)
      // println(last)
      assert(false, "duplicate entries")
    }

    pending = Nil
    top.state add cmds
    sink.exec(cmds, top.state)
  }

  def exec(cmd: Cmd, in: State) = {
    // println(cmd.getClass().getSimpleName())

    cmd match {
      case Push(n) =>
        flush(cmd, in)
        assert(pending.isEmpty)

        val add = List.tabulate(n) { _ => stack.head.copy }
        stack = add ++ stack
        sink.exec(cmd, top.state)

      case Pop(n) =>
        flush(cmd, in)
        assert(pending.isEmpty)

        stack = stack drop n
        sink.exec(cmd, top.state)

      case Reset =>
        flush(cmd, in)
        assert(pending.isEmpty)
        stack = reset
        sink.exec(cmd, top.state)

      case Exit =>
        ???

      // check-sat flushes, lemmas don't
      case CheckSat =>
        flush(cmd, in)
        assert(pending.isEmpty)
        sink.exec(cmd, top.state)

      // assume here that the model and labels are provided always by the backend,
      // perhaps we can find some more flexible option in the future.
      case Labels | GetModel | _: GetInfo =>
        sink.exec(cmd, top.state)

      case _ =>
        pending = cmd :: pending
        Success
    }
  }
}

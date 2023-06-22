package cuvee.pipe

import cuvee.util.Printer
import cuvee.smtlib._
import cuvee.State

object Pipe {
  def run(source: Source, sink: Sink, report: Report) {
    for (cmd <- source) {
      report { sink(cmd) }
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
  def copy(): Stage

  // executed with every check-sat/lemma command
  // returns the potentially modified script + an optional check command that
  // is then finally suggested to the backend sink
  def apply(prefix: List[Cmd], cmds: List[Cmd]): List[Cmd]
}

class Incremental(stage: Stage, sink: Sink) extends Sink {
  class Entry(var prefix: List[Cmd], val stage: Stage) {
    def copy() = new Entry(prefix, stage.copy())
  }

  var stack = List(new Entry(Nil, stage))
  def top = stack.head

  var pending: List[Cmd] = Nil

  def flush() = {
    val add = pending.reverse
    pending = Nil
    add
  }

  def exec(cmd: Cmd) = cmd match {
    case Push(n) =>
      val add = List.tabulate(n) { _ => stack.head.copy }
      stack = add ++ stack
      sink(cmd)

    case Pop(n) =>
      stack = stack drop n
      sink(cmd)

    // check-sat simply flushes
    case CheckSat =>
      val cmds = stage(top.prefix, flush())
      for (cmd <- cmds) sink(cmd)
      sink(cmd)

    case Lemma(expr, tactic, assert) =>
      pending = cmd :: pending
      val cmds = stage(top.prefix, flush())
      for (cmd <- cmds) sink(cmd)
      Success

    case GetModel =>
      // assume here that the model is provided always by the backend,
      // perhaps we can find some more flexible option in the future.
      sink(cmd)

    case _ =>
      pending = cmd :: pending
      Success
  }
}

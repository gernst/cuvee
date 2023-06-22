package cuvee.pipe

import cuvee.util.Printer
import cuvee.smtlib._
import cuvee.State

object Pipe {
  def run(source: Source, sink: Sink, report: Report) {
    for ((cmd, state) <- source) {
      report { sink(cmd, state) }
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
  // need to override for stateful components
  def copy(): Stage = this

  // executed with every check-sat/lemma command
  // returns the potentially modified script + an optional check command that
  // is then finally suggested to the backend sink

  def transform(prefix: List[Cmd], cmds: List[Cmd], state: State): (List[Cmd], Option[State])

  def apply(prefix: List[Cmd], cmds: List[Cmd], state: State): (List[Cmd], State) = {
    val (cmds_, state_) = transform(prefix, cmds, state)
    val state__ = state_.getOrElse { state.added(cmds_) }
    (cmds_, state__)
  }
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

  def exec(cmd: Cmd, state: State) = cmd match {
    case Push(n) =>
      val add = List.tabulate(n) { _ => stack.head.copy }
      stack = add ++ stack
      sink(cmd, state)

    case Pop(n) =>
      stack = stack drop n
      sink(cmd, state)

    // check-sat simply flushes
    case CheckSat =>
      val (cmds, state_) = stage(top.prefix, flush(), state)
      for (cmd <- cmds) sink(cmd, state_)
      sink(cmd, state_)

    case Lemma(expr, tactic, assert) =>
      pending = cmd :: pending
      val (cmds, state_) = stage(top.prefix, flush(), state)
      for (cmd <- cmds) sink(cmd, state_)
      Success

    case GetModel =>
      // assume here that the model is provided always by the backend,
      // perhaps we can find some more flexible option in the future.
      sink(cmd, state)

    case _ =>
      pending = cmd :: pending
      Success
  }
}

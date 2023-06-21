package cuvee.pipe

import cuvee.util.Printer
import cuvee.smtlib._
import cuvee.State

object Pipe {
  def run(source: Source, sink: Sink, report: Report) {
    for (cmd <- source) {
      report { sink.exec(cmd) }
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
  def copy: Stage

  // executed with every check-sat/lemma command
  // returns the potentially modified script + an optional check command that
  // is then finally suggested to the backend sink
  def apply(cmds: List[Cmd], check: Cmd): (List[Cmd], Cmd)
}

class Pipe(sink: Sink, stages: Stage*) extends Sink {
  // Note to self: if we want to keep the respective fixed prefixes, it needs to be per stage
  case class Entry(stages: List[Stage]) {
    def copy = Entry(stages map (_.copy))
  }

  var stack = List(Entry(stages.toList))
  var pending: List[Cmd] = Nil

  def flush(cmds: List[Cmd], check: Cmd, stages: List[Stage]): (List[Cmd], Cmd) =
    stages match {
      case Nil =>
        (cmds, check)

      case stage :: rest =>
        val (cmds_, check_) = stage.apply(cmds, check)
        flush(cmds, check, rest)
    }

  def exec(cmd: Cmd) = cmd match {
    case Push(n) =>
      val add = List.tabulate(n) { _ => stack.head.copy }
      stack = add ++ stack
      sink.exec(cmd)

    case Pop(n) =>
      stack = stack drop n
      sink.exec(cmd)

    case CheckSat | _: Lemma =>
      val (cmds, check) = flush(pending.reverse, cmd, stack.head.stages)
      for (cmd <- cmds)
        sink.exec(cmd)
      sink.exec(check)

    case GetModel =>
      // assume here that the model is provided always by the backend,
      // perhaps we can find some more flexible option in the future.
      sink.exec(cmd)

    case _ =>
      pending = cmd :: pending
      Success
  }
}

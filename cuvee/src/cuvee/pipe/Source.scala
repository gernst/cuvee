package cuvee.pipe

import cuvee.State
import cuvee.smtlib._
import java.io.Reader
import cuvee.util.Name
import cuvee.pure.Param
import cuvee.pure.Var
import java.io.FileReader
import java.io.InputStreamReader

trait Source extends Iterator[Cmd] {
  def hasNext: Boolean
  def next(): Cmd
}

object Source {
  def stdin = new smtlib(new InputStreamReader(System.in))

  def from(name: String) = {
    val reader = new FileReader(name)

    if (name endsWith ".bpl")
      new Source.boogie(reader)
    else if (name endsWith ".smt2")
      new Source.smtlib(reader)
    else
      cuvee.error("unknown file format: " + name)
  }

  class boogie(reader: Reader) extends Source {
    val from = {
      implicit val ctx: Map[Name, Param] = Map()
      implicit val scope: Map[Name, Var] = Map()
      val in = cuvee.boogie.scan(reader)
      cuvee.boogie.Grammar.cmd.iterator(in)
    }

    def hasNext: Boolean = from.hasNext
    def next(): Cmd = from.next()
  }

  class smtlib(reader: Reader) extends Source {
    val from = cuvee.sexpr.iterator(reader)
    val init = State.default
    val parser = new cuvee.smtlib.Parser(init)

    def hasNext = from.hasNext
    def next() = parser.cmd(from.next())
  }
}

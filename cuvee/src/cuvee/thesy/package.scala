package cuvee

import java.io.Reader
import cuvee.pipe.Source
import java.io.InputStreamReader
import java.io.FileReader
import java.io.StringReader
import cuvee.pure.Expr
import cuvee.smtlib.Solver
import java.io.BufferedReader
import cuvee.smtlib.Cmd

package object thesy {
  implicit val printer: cuvee.util.Printer = cuvee.thesy.Printer

  def parse(file: String) = {
    val in = source(file)
    val cmds = in.toList
    val st = in.state
    (cmds, st)
  }

  def source(): Source = source(new InputStreamReader(System.in))
  def source(path: String): Source = source(new FileReader(path))

  def source(reader: Reader): Source = new Source {
    val from = cuvee.sexpr.iterator(reader)
    val init = State.default
    val parser = new cuvee.thesy.Parser(init)

    def state = parser.st
    def hasNext = from.hasNext
    def next() = parser.cmd(from.next)
  }

  def storedLemmas(th: String, st: State) = {
    val in = new BufferedReader(new FileReader(th))
    readLemmas(in, st)
  }

  def readLemmas(in: BufferedReader, st: State) = {
    val PROVED = "proved: "
    val parser = new Parser(st)

    var line = in.readLine()
    var lemmas: List[Expr] = Nil

    while (line != null) {
      val pos = line.indexOf(PROVED)
      if (pos >= 0) {
        val rest = line.substring(pos + PROVED.length)
        val from = cuvee.sexpr.parse(new StringReader(rest))
        val eq = parser.rule(from)
        val expr = eq.toExpr

        lemmas = expr :: lemmas
      }

      line = in.readLine()
    }

    lemmas.reverse
  }
}

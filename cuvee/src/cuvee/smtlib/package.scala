package cuvee

import java.io.InputStreamReader
import cuvee.pipe.Source
import java.io.Reader
import java.io.FileReader
import cuvee.sexpr.Printer


package object smtlib {
  def parse(file: String): (List[Cmd], State) = {
    val from = sexpr.parse(file)
    val st = State.default
    val res = parse(from, st)
    (res, st)
  }

  def parse(from: List[sexpr.Expr], st: State): List[Cmd] = {
    val parser = new Parser(st)
    val res = parser.cmds(from)
    res
  }

  def source() : Source = source(new InputStreamReader(System.in))
  def source(path: String): Source  = source(new FileReader(path))

  def source(reader: Reader): Source  = new Source {
    val from = cuvee.sexpr.iterator(reader)
    val init = State.default
    val parser = new cuvee.smtlib.Parser(init)

    def hasNext = from.hasNext
    def next() = parser.cmd(from.next())
  }

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = Printer
}

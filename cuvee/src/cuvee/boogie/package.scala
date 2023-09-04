package cuvee

import cuvee.pure._
import cuvee.util.Name
import cuvee.smtlib._
import java.io.FileReader
import java.io.Reader
import easyparse.Token
import scala.collection.mutable.ListBuffer
import cuvee.sexpr.Tok
import cuvee.pipe.Source

package object boogie {
  def scan(file: String): Seq[Token] = {
    scan(new FileReader(file))
  }

  def scan(reader: Reader): Seq[Token] = {
    val scanner = new boogie.Scanner(reader)
    val iterator = new ScannerIterator(scanner)
    val stream = Stream.fromIterator(iterator)
    stream.toList
  }

  def parse(file: String): (List[Cmd], State) = {
    val in = scan(file)

    implicit val ctx: Map[Name, Param] = Map()
    implicit val scope: Map[Name, Var] = Map()
    Grammar.script.parseAll(in)
  }

  def source(path: String) = new Source {
    val from = {
      implicit val ctx: Map[Name, Param] = Map()
      implicit val scope: Map[Name, Var] = Map()
      val reader = new FileReader(path)
      val in = cuvee.boogie.scan(reader)
      cuvee.boogie.Grammar.cmd.iterator(in)
    }

    def state = cuvee.boogie.Parser.state
    def hasNext = from.hasNext
    def next() = from.next()
  }

  class ScannerIterator(scanner: boogie.Scanner) extends Iterator[Token] {
    // buffers one next token in case hasNext had been called
    var token: Option[Token] = None

    def next() = {
      if (hasNext) {
        val Some(result) = token
        token = None
        result
      } else {
        throw new NoSuchElementException("next() at end of input")
      }
    }

    def tryNext() {
      token = scanner.next() match {
        case null => None
        case next => Some(next)
      }
    }

    def hasNext = {
      if (token == None)
        tryNext()
      token != None
    }
  }

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = cuvee.boogie.Printer
}

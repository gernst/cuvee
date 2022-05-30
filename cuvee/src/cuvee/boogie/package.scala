package cuvee

import cuvee.pure._
import cuvee.smtlib._
import java.io.FileReader
import java.io.Reader
import arse.Token
import scala.collection.mutable.ListBuffer
import cuvee.sexpr.Tok

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
    Parser.script.parseAll(in)
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
}

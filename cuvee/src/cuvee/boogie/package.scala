package cuvee

import cuvee.pure._
import cuvee.smtlib._
import java.io.FileReader
import java.io.Reader
import arse.Token
import scala.collection.mutable.ListBuffer
import cuvee.sexpr.Tok

package object boogie {
  def scan(file: String): List[Token] = {
    scan(new FileReader(file))
  }

  def scan(reader: Reader): List[Token] = {
    val scanner = new boogie.Scanner(reader)
    val result = new ListBuffer[Token]()

    var token = scanner.next()
    while (token != Parser.eof) {
      result += token
      token = scanner.next()
    }

    result.toList
  }

  def parse(file: String): List[Cmd] = {
    val in = scan(file)
    val from = Parser.cmds.parseAll(in)
    from
  }
}

package cuvee.sexpr

import scala.collection.mutable
import java.io.StringReader
import java.io.Reader
import java.io.File
import java.io.FileReader

class Parser(scanner: Scanner) {
  var tok: Tok = null
  var peek: Tok = null

  next

  def next = {
    tok = peek
    peek = scanner.next
    tok
  }

  def check(tok: Tok) = {
    next match {
      case `tok` =>
    }
  }

  def sexpr(): Expr = {
    next match {
      case Tok.lp =>
        val args = sexprs()
        check(Tok.rp)
        App(args)
      case atom: Atom =>
        atom
    }
  }

  def sexprs(): List[Expr] = {
    val buf = mutable.ListBuffer[Expr]()

    while (peek != Tok.eof && peek != Tok.rp) {
      buf += sexpr()
    }

    buf.toList
  }

  def eof() {
    check(Tok.eof)
  }
}

object Parser {
  def apply(reader: Reader): Parser = {
    val scanner = new Scanner(reader)
    val parser = new Parser(scanner)
    parser
  }

  def apply(data: String): Parser = {
    val reader = new StringReader(data)
    Parser(reader)
  }

  def apply(file: File): Parser = {
    val reader = new FileReader(file)
    Parser(reader)
  }

  def sexpr(str: String) = {
    val parser = Parser(str)
    val result = parser.sexpr()
    parser.eof()
    result
  }

  def sexprs(str: String) = {
    val parser = Parser(str)
    val result = parser.sexprs()
    parser.eof()
    result
  }

  def main(args: Array[String]) {
    println(sexprs(""))
    println(sexprs("0 1 12 0.0 0.01 0x1 0x12 #b0 #b01"))
    println(sexprs("a ab |a| |ab| = < |< >|"))
    println(sexprs("\"\" \"a\" \"ab\""))
    println(sexprs("() (a) (a b)"))
  }
}

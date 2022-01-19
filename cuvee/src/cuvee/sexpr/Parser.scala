package cuvee.sexpr

import scala.collection.mutable
import java.io.StringReader
import java.io.Reader
import java.io.File
import java.io.FileReader

import cuvee.fail

object Parser_ {
  import arse._
  import arse.implicits._

  val expr: arse.Parser[Expr, Token] =
    P(app | atom)

  val atom = tok[Token] collect { case atom: Atom =>
    atom
  }

  val app =
    App.from(Tok.lp ~ expr.+ ~ Tok.rp)
}

class Parser(scanner: Scanner) {
  import arse.Token

  var _tok: Token = null
  var _peek: Token = null

  def peek() = {
    if (_peek == null) // consume next token only when needed
      _peek = scanner.next
    _peek
  }

  def next() = {
    if (_peek == null) {
      _tok = scanner.next
    } else {
      _tok = _peek
      _peek = null
    }
    _tok
  }

  def check(tok: Token) = {
    next match {
      case `tok` =>
      // ok
      case tok =>
        fail("unexpected token: " + tok)
    }
  }

  def sexpr(): Expr = {
    next match {
      case Tok.lp =>
        val args = sexprs()
        check(Tok.rp)
        App(args: _*)
      case atom: Atom =>
        atom
      case tok =>
        fail("unexpected token: " + tok)
    }
  }

  def sexprs(): List[Expr] = {
    val buf = mutable.Buffer[Expr]()

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
}

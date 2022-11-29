package cuvee.sexpr

import scala.collection.mutable
import java.io.StringReader
import java.io.Reader
import java.io.File
import java.io.FileReader

import cuvee.error

object Parser_ {
  import easyparse._
  import easyparse.implicits._

  val expr: easyparse.Parser[Expr, Token] =
    P(app | atom)

  val atom = tok[Token] collect { case atom: Atom =>
    atom
  }

  val app =
    App.from(Tok.lp ~ expr.+ ~ Tok.rp)
}

class Parser(scanner: Scanner) {
  import easyparse.Token

  var _tok: Token = null
  var _peek: Token = null

  def shift() = {
    val r = scanner.next
    r
  }

  def peek() = {
    if (_peek == null) // consume next token only when needed
      _peek = shift()
    _peek
  }

  def next() = {
    if (_peek == null) {
      _tok = shift()
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
        error("unexpected token: " + tok)
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
        error("unexpected token: " + tok)
    }
  }

  def sexprs(): List[Expr] = {
    val buf = mutable.Buffer[Expr]()

    while (peek != Tok.eof && peek != Tok.rp) {
      buf += sexpr()
    }

    buf.toList
  }

  def eof(): Unit = {
    check(Tok.eof)
  }

  // only one instance per parser
  object iterator extends Iterator[Expr] {
    def hasNext = {
      peek == Tok.eof
    }

    def next() = {
      sexpr()
    }
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

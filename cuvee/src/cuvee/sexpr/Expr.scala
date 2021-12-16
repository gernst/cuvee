package cuvee.sexpr

sealed trait Tok
sealed trait Expr
sealed trait Atom extends Expr with Tok

object Expr {
  // access functions for the scanner
  def eof = Tok.eof
  def lp = Tok.lp
  def rp = Tok.rp
}

object Tok {
  case object eof extends Tok
  case object lp extends Tok
  case object rp extends Tok
}

object Lit {
  case class bin(digits: String) extends Atom
  case class dec(digits: String) extends Atom
  case class num(digits: String) extends Atom
  case class hex(digits: String) extends Atom

  case class str(value: String) extends Atom
}

case class Id(name: String) extends Atom
case class Kw(name: String) extends Atom

case class App(args: Expr*) extends Expr


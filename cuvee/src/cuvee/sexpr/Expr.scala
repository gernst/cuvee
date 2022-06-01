package cuvee.sexpr

import arse._

sealed trait Expr {
  def apply(index: Int) =
    this match {
      case App(args @ _*) => args(index)
    }

  def replace(re: Map[String, Expr]): Expr
}

sealed trait Atom extends Expr with Token {}
sealed trait Lit extends Atom {
  def replace(re: Map[String, Expr]) = this
}

object Tok {
  val lp = KW("(")
  val rp = KW(")")
  def kw(n: String) = KW(n) // parser

  val eof = new Token {}
}

object Lit {
  val zero = num("0")

  case class bin(digits: String) extends Lit { }
  case class dec(digits: String) extends Lit { }
  case class num(digits: String) extends Lit { }
  case class hex(digits: String) extends Lit { }
  case class str(digits: String) extends Lit { }
}

case class Kw(name: String) extends Lit { }

case class Id(name: String) extends Atom {
  def replace(re: Map[String, Expr]) = re getOrElse (name, this)
}

object App {
  val from = (args: List[Expr]) => App(args: _*)
}

case class App(args: Expr*) extends Expr {
  def replace(re: Map[String, Expr]) =
    App(args map (_ replace re): _*)
}

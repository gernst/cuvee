package cuvee.sexpr

import arse._

sealed trait Expr extends cuvee.sexpr.Syntax {
  def apply(index: Int) =
    this match {
      case App(args @ _*) => args(index)
    }

  def replace(re: Map[String, Expr]): Expr
}

sealed trait Atom extends Expr with Token {}

sealed trait Lit extends Atom {
  def sexpr = List(toString)
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

  case class bin(digits: String) extends Lit {
    override def toString = "#b" + digits
  }

  case class dec(digits: String) extends Lit {
    override def toString = digits
  }

  case class num(digits: String) extends Lit {
    override def toString = digits
  }

  case class hex(digits: String) extends Lit {
    override def toString = "0x" + digits
  }

  case class str(digits: String) extends Lit {
    override def toString = "\"" + digits + "\""
  }
}

case class Kw(name: String) extends Atom {
  def replace(re: Map[String, Expr]) = this
  def sexpr = ":" + name
  override def toString = ":" + name
}

case class Id(name: String) extends Atom {
  def replace(re: Map[String, Expr]) = re getOrElse (name, this)
  def sexpr = List(name)
  override def toString = name
}

object App {
  val from = (args: List[Expr]) => App(args: _*)
}

case class App(args: Expr*) extends Expr {
  def sexpr = List(args: _*)
  def replace(re: Map[String, Expr]) =
    App(args map (_ replace re): _*)
  override def toString =
    args.mkString("(", " ", ")")
}

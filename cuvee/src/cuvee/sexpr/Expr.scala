package cuvee.sexpr

sealed trait Tok

sealed trait Expr {
  def lines: List[String]
}

sealed trait Atom extends Expr with Tok {}

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
  case class bin(digits: String) extends Atom {
    def lines = List("#%b" + digits)
  }
  case class dec(digits: String) extends Atom {
    def lines = List(digits)
  }
  case class num(digits: String) extends Atom {
    def lines = List(digits)
  }
  case class hex(digits: String) extends Atom {
    def lines = List("0x" + digits)
  }
  case class str(digits: String) extends Atom {
    def lines = List("\"" + digits + "\"")
  }
}

case class Id(name: String) extends Atom {
  def lines = List(mangle(name))
}

case class Kw(name: String) extends Atom {
  def lines = List(":" + name)
}

case class App(args: Expr*) extends Expr {
  def lines = {
    val strings =
      args.toList flatMap (_.lines)

    val max = strings.maxBy(_.length)
    val sum = strings.foldLeft(0)(_ + _.length)

    val break =
      strings.length >= 2 && (max.length > 20 || sum >= 80)

    if (break) {
      val first :: rest = strings
      ("(" + first) :: indent(rest)
    } else {
      List(strings.mkString("(", " ", ")"))
    }
  }

  def indent(lines: List[String]): List[String] = lines match {
    case List(last) =>
      List("  " + last + ")")

    case first :: rest =>
      ("  " + first) :: indent(rest)
  }
}

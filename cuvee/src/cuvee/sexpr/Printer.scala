package cuvee.sexpr

import cuvee.error

trait Syntax {
  def sexpr: Any

  def lines: List[String] = Printer.print(sexpr)
}

class SyntaxList(xs: List[Syntax]) {
  def sexpr = xs map (_.sexpr)
}

object Printer {

  def print(any: Any): List[String] = any match {
    // Boolean values
    case true        => List("true")
    case false       => List("false")
    // Numbers
    case i: Int      => List(i.toString)
    case i: BigInt   => List(i.toString)
    case f: Float    => List(f.toString)
    // Syntax (recursive call on the syntax' s-expression)
    case s: Syntax   => print(s.sexpr)
    // String (= Id)
    case s: String   => List(cuvee.sexpr.mangle(s))
    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => printApp(print(a) ++ print(b))
    case xs: List[_] => printApp(xs flatMap print)
  }

  def printApp(args: List[String]): List[String]= {
    if (args.isEmpty) {
      List("()")
    } else {
      val max = args.maxBy(_.length)
      val sum = args.foldLeft(0)(_ + _.length)

      val break =
        args.length >= 2 && (max.length > 20 || sum >= 80)

      if (break) {
        val first :: rest = args
        ("(" + first) :: indent(rest)
      } else {
        List(args.mkString("(", " ", ")"))
      }
    }
  }

  def indent(lines: List[String]): List[String] = lines match {
    case List(last)    => List("  " + last + ")")
    case first :: rest => ("  " + first) :: indent(rest)
  }
}

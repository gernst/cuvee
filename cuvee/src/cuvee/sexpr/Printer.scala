package cuvee.sexpr

import cuvee.error
import cuvee.util.Name

object Printer extends cuvee.util.Printer {
  def lines(any: Any): List[String] = any match {
    // Boolean values
    case true        => List("true")
    case false       => List("false")
    // Numbers
    case i: Int      => List(i.toString)
    case i: BigInt   => List(i.toString)
    case f: Float    => List(f.toString)
    // Name
    case n: Name     => List(cuvee.sexpr.mangle(n.toLabel))
    case s: String   => List(s)
    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => printApp(lines(a) ++ lines(b))
    case xs: List[_] => printApp(xs flatMap lines)
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

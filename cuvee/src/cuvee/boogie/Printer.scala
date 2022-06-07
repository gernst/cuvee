package cuvee.boogie

import cuvee.error
import cuvee.util
import cuvee.pure._

trait Syntax extends util.Syntax {
  def bexpr: List[Any]
}

object Printer extends cuvee.util.Printer {
  def lines(any: Any): List[String] = any match {
    // Boolean values
    case true        => List("true")
    case false       => List("false")
    // Numbers
    case i: Int      => List(i.toString)
    case i: BigInt   => List(i.toString)
    case f: Float    => List(f.toString)
    // Syntax (recursive call on the syntax' s-expression)
    case s: Syntax   => lines(s.bexpr)
    // String (= Id)
    case s: String   => List(s)
    // Applications, either represented by a pair (a, b) or a list
    case (a, b)      => lines(a) ++ lines(b)
    case xs: List[_] => xs flatMap lines
    case _ => List()
  }
}

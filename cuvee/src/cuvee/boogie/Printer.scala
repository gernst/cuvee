package cuvee.boogie

import cuvee.error
import cuvee.util
import cuvee.pure._
import cuvee.util.Name

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
    // Name
    case n: Name     => List(n.toLabel)
    // Syntax (recursive call on the syntax' s-expression)
    case s: Syntax   => lines(s.bexpr)
    // String (= Id)
    case s: String   => List(s)
    // Syntax (recursive call on the syntax' s-expression)
    case s: Syntax   => lines(s.bexpr)
    // Pairs and lists consist of tokens and more syntax elements
    // Call lines on the elements recursively
    case (a, b)      => lines(a) ++ lines(b)
    case xs: List[_] => List((xs flatMap lines).mkString)
    // Fall-through: just crash
    // case _ => List()
  }
}

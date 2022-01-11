package cuvee.sexpr

trait Syntax {
  def sexpr: Any
  def lines = Printer.print(sexpr).lines
}

class SyntaxList(xs: List[Syntax]) {
  def sexpr = xs map (_.sexpr)
}

object Printer {
  def print(any: Any): Expr = any match {
    case true =>
      True
    case false =>
      False
    case s: Syntax =>
      print(s.sexpr)
    case i: Int =>
      Lit.num(i.toString)
    case i: Float =>
      Lit.dec(i.toString)
    case s: String =>
      Id(s)
    case (a, b) =>
      App(print(a), print(b))
    case xs: List[_] =>
      App(xs map print: _*)
  }
}

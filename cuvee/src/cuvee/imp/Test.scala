package cuvee.imp

import cuvee.pure._
import cuvee.smtlib.printer

object Test {
  def main(args: Array[String]) {
    val x = Var("x", Sort.int)
    val y = Var("y", Sort.int)

    val pre = (Zero <= x)
    val body = Assign(List(x, y), List(x - One, y + One))
    val term = x
    val inv = (Zero <= x)
    val post = y === (Old(x) + Old(y))

    val prog = While(Zero < x, body, term, inv, post, Nil)

    val xs = List(x, y)
    val st = Expr.id(xs)

    val phi = Forall(xs, pre ==> Eval.wp(WP, prog, st, post, List(st)))

    for (line <- phi.lines)
      println(line)
  }
}

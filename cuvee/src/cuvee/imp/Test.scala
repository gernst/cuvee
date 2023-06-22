package cuvee.imp

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._

object Test {
  def main(args: Array[String]) {
    val x = Var("x", Sort.int)
    val y = Var("y", Sort.int)

    val pre = (Zero <= x)
    val body = Assign(List(x, y), List(x - One, y + One))
    val term = x
    val inv = (Zero <= x) && ((x + y) === (Old(x) + Old(y)))
    val sum = True
    val post = y === (Old(x) + Old(y))

    val prog = While(Zero < x, body, term, inv, sum, Nil)

    val xs = List(x, y)
    val st = Expr.id(xs)

    val eval = new Eval(State.default)
    val phi = Forall(xs, pre ==> eval.wp(WP, prog, st, post, List(st)))

    val solver = Solver.z3()

    for (line <- phi.lines)
      println(line)

    println(solver.check(!phi))
  }
}

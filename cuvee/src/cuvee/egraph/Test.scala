package cuvee.egraph

import cuvee.pure._

object Test {
  def main(args: Array[String]) {
    val g = new EGraph()
    g.debug = true

    val a = Param("a")
    val list_a = Fun.list_a

    val n = Var("n", Sort.int)

    val x = Var("x", a)
    val y = Var("y", a)

    val xs = Var("xs", list_a)
    val ys = Var("ys", list_a)

    val nil = Const(Fun.nil, list_a)

    val id = Fun("id", List(a), List(a), a)
    val append = Fun("append", List(a), List(list_a, list_a), list_a)

    val length = Fun("length", List(a), List(list_a), Sort.int)
    val length_ = Fun("length_", List(a), List(list_a, Sort.int), Sort.int)

    val rules = List(
      Rule(length(xs), length_(xs, Zero)),
      Rule(length_(xs, n), length_(xs, Zero) + n, True, List(n -> Zero)),
      Rule(length(append(xs, ys)), length_(xs, length_(ys, Zero)))
    )

    val e = length(append(xs, ys))
    val c = g.add(e)

    for (ec <- g.classes)
      println(ec)
    println()

    g.rewrite(rules)
    g.rewrite(rules)
    g.rewrite(rules map (_.flip))
    println()

    for (ec <- g.classes)
      println(ec.id + ": " + ec)
    println()

  }
}

package cuvee.egraph

import cuvee.pure._

object Test {
  def main(args: Array[String]) {
    test1()
  }

  def test1() {
    val g = new EGraph()
    // g.debug = true

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
      Rule(n + Zero, n),
      Rule(length(xs), length_(xs, Zero)),
      Rule(length_(xs, n), length_(xs, Zero) + n, True, List(n -> Zero)),
      Rule(length(append(xs, ys)), length_(xs, length_(ys, Zero)))
    )

    val original = List(id, append, length, Fun.plus)

    def consider(nd: g.ENode) = nd match {
      case g.EApp(Inst(fun, _), _) =>
        original contains fun
      case _ =>
        true
    }

    val e = length(append(xs, ys))
    val c = g.add(e)

    var cs: Set[g.EClass] = Set()

    var i = 0
    var done = false
    val all = rules ++ (rules flatMap (_.maybeFlip))

    while (!done) {
      i += 1
      done = g.rewrite(all)
      println("round " + i + " (new: " + !done + ")")
    }

    // for ((id, ec) <- g.classes) {
    //   println("class")
    //   for (nd <- ec.nodes)
    //     println("  " + nd)
    // }

    for ((id, ec) <- g.classes) {
      println("class")
      for (expr <- g.extract(id, consider))
        println("  " + expr)
    }
  }



  def test2() {
    val g = new EGraph()

    val a = Param("a")
    val list_a = Fun.list_a

    val xs = Var("xs", list_a)
    val ys = Var("ys", list_a)

    val x = Var("x", a)
    val y = Var("y", a)

    val nil = Const(Fun.nil, list_a)
    val cons = Fun.cons

    val id = Fun("id", List(a), List(a), a)
    val append = Fun("append", List(a), List(list_a, list_a), list_a)

    val equations = List(
      id(xs) -> xs,
      append(xs, nil) -> id(xs),
      append(nil, ys) -> ys,
      append(cons(x, xs), ys) -> ys
    )

    for ((lhs, rhs) <- equations) {
      g.merge(lhs, rhs)
    }

    g.rebuild()

    for ((id, ec) <- g.classes) {
      println("class $" + id.id)
      for (expr <- ec.nodes)
        println("  " + expr)
    }
    println()

    val unifiers = for (
      (nd1 @ g.EApp(inst1, _), id1) <- g.hash;
      (nd2 @ g.EApp(inst2, _), id2) <- g.hash
      if id1 != id2 && inst1.fun == inst2.fun;
      su <- g.eunify(nd1, nd2) if su.nonEmpty
    ) yield {
      (su, id1, id2)
    }

    for((su, id1, id2) <- unifiers) {
      println("unify " + id1 + " and " + id2 + " with " + su)
    }
  }

}

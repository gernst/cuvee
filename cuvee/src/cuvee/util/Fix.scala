package cuvee.util

import scala.collection.mutable

object Fix {
  def main(args: Array[String]) {
    val graph = List(
      "x" -> List("y"),
      "y" -> List("z", "x"),
      "z" -> List("y")
    )

    val (a, b, c) = rtc(graph)
    println(a)
    println(b)
    println(c)
  }

  def init[X](succ: Iterable[(X, Iterable[X])]) = {
    val grouped = succ.groupBy { case (k, vs) => k }

    val flat = grouped.map { case (k, vvs) =>
      val vs = vvs flatMap (_._2)
      k -> vs
    }

    flat withDefaultValue (Iterable())
  }

  def rtc[X](succ: Iterable[(X, Iterable[X])]) = {
    val map = init(succ)
    digraph(map.keys, (x: X) => Iterable(x), map)
  }

  def tc[X](succ: Iterable[(X, Iterable[X])]) = {
    val map = init(succ)
    digraph(map.keys, map, map)
  }

  def digraph[X, A](
      from: X,
      init: X => Iterable[A],
      succ: X => Iterable[X]
  ): (List[X], mutable.Map[X, mutable.Set[X]], mutable.Map[X, mutable.Set[A]]) = {
    digraph(Iterable(from), init, succ)
  }

  def digraph[X, A](
      from: Iterable[X],
      init: X => Iterable[A],
      succ: X => Iterable[X]
  ): (List[X], mutable.Map[X, mutable.Set[X]], mutable.Map[X, mutable.Set[A]]) = {
    val stack = mutable.Stack[X]()
    val depth = mutable.Map[X, Int]()
    val result = mutable.Map[X, mutable.Set[A]]()
    var order = Nil: List[X]
    val sccs = mutable.Map[X, mutable.Set[X]]()

    for (x <- from) {
      start(x)
    }

    def start(x: X) {
      if (!(depth contains x))
        traverse(x)
    }

    def traverse(x: X) {
      stack push x
      val d = stack.length

      depth(x) = d
      result(x) = mutable.Set()
      result(x) ++= init(x)

      for (y <- succ(x)) {
        start(y)

        depth(x) = Math.min(depth(x), depth(y))
        result(x) = result(x) union result(y)
      }

      if (depth(x) == d) {
        sccs(x) = mutable.Set()
        order = x :: order

        do {
          val y = stack.top
          sccs(x) += y
          depth(y) = Int.MaxValue
          result(y) = result(x)
        } while (stack.pop() != x)
      }
    }

    (order.reverse, sccs, result)
  }
}

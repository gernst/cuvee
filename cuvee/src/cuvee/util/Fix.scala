package cuvee.util

import scala.collection.mutable

object Fix {
  def rtc[X](succ: Iterable[(X, Iterable[X])]) = {
    val map = succ.toMap withDefaultValue (Iterable())
    digraph(map.keys, (x: X) => Iterable(x), map)
  }

  def tc[X](succ: Iterable[(X, Iterable[X])]) = {
    val map = succ.toMap withDefaultValue (Iterable())
    digraph(map.keys, map, map)
  }

  def digraph[X, A](
      states: Iterable[X],
      init: X => Iterable[A],
      succ: X => Iterable[X]
  ): mutable.Map[X, mutable.Set[A]] = {
    val stack = mutable.Stack[X]()
    val depth = mutable.Map[X, Int]()
    val result = mutable.Map[X, mutable.Set[A]]()

    for (x <- states) {
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
        do {
          val y = stack.top
          depth(y) = Int.MaxValue
          result(y) = result(x)
        } while (stack.pop() != x)
      }
    }

    result
  }
}

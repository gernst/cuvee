package cuvee.imp

import cuvee.pure._

package object traces {
  object sig {
    val a = Param("a")

    val current = Fun("current", List(a), List(a, Sort.int, Sort.trace(a)), Sort.bool)
    val count = Fun("count", Nil, List(Sort.int, Sort.int), Sort.trace(Sort.int))
    val range = Fun("range", Nil, List(Sort.int, Sort.int, Sort.int), Sort.trace(Sort.int))

    // val cons = List(Con.trace)
    // val funs = List(current, count, range)
  }

  object Current extends Sugar.ternary(sig.current)
  object Count extends Sugar.binary(sig.count)
  object Range extends Sugar.ternary(sig.range)
}

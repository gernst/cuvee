package cuvee.lemmas.recognize

import cuvee.pure._
import cuvee.lemmas.Def

object Same {
  import cuvee.util.Matching

  def known(df: Def, args: List[Expr], dg: Def): Option[List[Expr]] = {
    val noParams = df.params.isEmpty && dg.params.isEmpty // currently not supported
    val sameType = df.typ == dg.typ
    val sameArity = df.arity == dg.arity

    if (noParams && sameType && sameArity) {
      val is = List(0 until df.arity: _*)
      val js = List(0 until dg.arity: _*)
      assert(is.length == js.length)

      def casesHaveAllSamePatterns(i: Int, j: Int): List[(Int, Int)] = {
        ???
      }

      Matching.relate(is, js, casesHaveAllSamePatterns)
      ???
    } else {
      None
    }
  }
}

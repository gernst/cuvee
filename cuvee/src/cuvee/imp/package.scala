package cuvee

import cuvee.pure._

package object imp {
  val a = Param("a")
  val old = Fun("old", List(a), List(a), a)

  implicit def toProgList(progs: List[Prog]) = new ProgList(progs)
}

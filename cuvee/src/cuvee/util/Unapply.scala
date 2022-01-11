package cuvee.util

object Map_ {
  def unapplySeq[A, B](map: Map[A, B]) = {
    Some(map.toSeq)
  }
}

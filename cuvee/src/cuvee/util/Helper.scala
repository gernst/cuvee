package cuvee.util

class HelperList[T](val list: List[T]) {
  def partitionCount(p: T => Boolean): (Int, Int) = {
    (0, 0)
  }
}

object Helper {
  implicit def toHelperList[T](l: List[T]) = new HelperList(l);

  def intersperse(list: List[Any], inner: Any): List[Any] = list match {
    case fst :: snd :: rest => fst :: inner :: intersperse(snd :: rest, inner)
    case fst :: Nil         => List(fst)
    case _                  => List()
  }

  def intersperse(
      list: List[Any],
      left: Any,
      inner: Any,
      right: Any
  ): List[Any] = left :: intersperse(list, inner) ::: List(right)
}

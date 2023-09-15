package cuvee.util

object Matching {
  // API without state S
  def relate[K, A, B, M](
      ks: Set[K],
      as: Map[K, List[A]],
      bs: Map[K, List[B]],
      f: (A, B) => List[M]
  ): List[(List[(A, B, M)], List[A], List[B])] = {
    val common = as.keySet & bs.keySet
    val all = as.keySet | bs.keySet
    ???
  }

  def relate[A, B, AB](
      as: List[A],
      bs: List[B],
      f: (A, B) => List[AB]
  ): List[(List[AB], List[A], List[B])] = as match {
    case Nil =>
      List((Nil, Nil, bs))

    case a :: as =>
      val here =
        for (
          (ab, b, bs_) <- relate(a, bs, f);
          (abs, as__, bs__) <- relate(as, bs_, f)
        )
          yield (ab :: abs, as__, bs__)

      val there =
        for ((abs, as_, bs_) <- relate(as, bs, f))
          yield (abs, a :: as_, bs_)

      here ++ there
  }

  def relate[A, B, AB](
      a: A,
      bs: List[B],
      f: (A, B) => List[AB]
  ): List[(AB, B, List[B])] = bs match {
    case Nil =>
      Nil

    case b :: bs =>
      val here =
        for ((ab, b) <- relate(a, b, f))
          yield (ab, b, bs)

      val there =
        for ((ab, b_, bs_) <- relate(a, bs, f))
          yield (ab, b_, b :: bs_)

      here ++ there
  }

  def relate[A, B, AB](
      a: A,
      b: B,
      f: (A, B) => List[AB]
  ): List[(AB, B)] = {
    for (ab <- f(a, b))
      yield (ab, b)
  }

  // API that tracks state S
  def relate[K, A, B, M, S](
      ks: Set[K],
      as: Map[K, List[A]],
      bs: Map[K, List[B]],
      st: S,
      f: (A, B, S) => List[(M, S)]
  ): List[(List[(A, B, M)], List[A], List[B], S)] = {
    val common = as.keySet & bs.keySet
    val all = as.keySet | bs.keySet
    ???
  }

  def relate[A, B, AB, S](
      as: List[A],
      bs: List[B],
      st: S,
      f: (A, B, S) => List[(AB, S)]
  ): List[(List[AB], List[A], List[B], S)] = as match {
    case Nil =>
      List((Nil, Nil, bs, st))

    case a :: as =>
      val here =
        for (
          (ab, b, bs_, st_) <- relate(a, bs, st, f);
          (abs, as__, bs__, st__) <- relate(as, bs_, st_, f)
        )
          yield (ab :: abs, as__, bs__, st__)

      val there =
        for ((abs, as_, bs_, st_) <- relate(as, bs, st, f))
          yield (abs, a :: as_, bs_, st_)

      here ++ there
  }

  def relate[A, B, AB, S](
      a: A,
      bs: List[B],
      st: S,
      f: (A, B, S) => List[(AB, S)]
  ): List[(AB, B, List[B], S)] = bs match {
    case Nil =>
      Nil

    case b :: bs =>
      val here =
        for ((ab, b, st_) <- relate(a, b, st, f))
          yield (ab, b, bs, st_)

      val there =
        for ((ab, b_, bs_, st_) <- relate(a, bs, st, f))
          yield (ab, b_, b :: bs_, st_)

      here ++ there
  }

  def relate[A, B, AB, S](
      a: A,
      b: B,
      st: S,
      f: (A, B, S) => List[(AB, S)]
  ): List[(AB, B, S)] = {
    for ((ab, st_) <- f(a, b, st))
      yield (ab, b, st_)
  }
}

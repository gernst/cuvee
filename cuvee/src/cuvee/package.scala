import scala.annotation.tailrec

package object cuvee {
  def error(msg: => String) = {
    require(false, msg)
    ???
  }

  def trace[A](msg: => String)(f: => A) = {
    try {
      f
    } catch {
      case t: Throwable =>
        println("trace: " + msg)
        throw t
    }
  }

  def undefined(implicit
      file: sourcecode.File,
      line: sourcecode.Line,
      enclosing: sourcecode.Enclosing,
      name: sourcecode.Name
  ) = {
    println("internal error: an implementation is missing")
    println("  " + file.value + ":" + line.value)
    println("  in " + enclosing.value)
    error("missing implementation: " + enclosing.value)
  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None        => self
      case Some(index) => this __ index
    }

    def ~~(index: Option[Int]): String = index match {
      case None        => self
      case Some(index) => self + "$" + index
    }
  }

  def Union[A](xs: Iterable[Set[A]]): Set[A] =
    xs.reduce(_ union _)

  def Intersect[A](xs: Iterable[Set[A]]): Set[A] =
    xs.reduce(_ intersect _)

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }

    def intersects(that: Set[A]) = {
      (self & that).nonEmpty
    }
  }

  implicit class ListOps[A](self: List[A]) {
    def intersperse[B >: A](inner: B): List[B] = self match {
      case fst :: snd :: rest =>
        fst :: inner :: ((snd :: rest) intersperse inner)
      case fst :: Nil => List(fst)
      case _          => List()
    }

    def intersperse[B >: A](left: B, inner: B, right: B): List[B] =
      left :: (self intersperse inner) ::: List(right)

    def removed(pos: Int) =
      self.patch(pos, Nil, 1)
  }

  implicit class ListMapOps[A, B](self: List[Map[A, B]]) {
    def merged = {
      self.fold(Map())(_ ++ _)
    }
  }

  @tailrec
  def fix[A](f: Set[A] => Set[A], as: Set[A] = Set.empty[A]): Set[A] = {
    val as_ = f(as)
    if (as == as_) as
    else fix(f, as_)
  }

  def seq[A](f: => A, last: A = null): Seq[A] = {
    val builder = Seq.newBuilder[A]
    var a = f

    while (a != last) {
      builder += a
      a = f
    }

    builder.result
  }

  def selections[A](xss: List[A]): LazyList[(A, List[A])] = xss match {
    case Nil => LazyList.empty
    case x :: xs =>
      (x, xs) #:: (for ((y, ys) <- selections(xs))
        yield (y, x :: ys))
  }

  def permute[A](xs: List[A]): LazyList[List[A]] = xs match {
    case Nil => LazyList(Nil)

    case t :: Nil      => LazyList(xs)
    case t :: u :: Nil => LazyList(xs, List(u, t))

    case _ =>
      for ((y, ys) <- selections(xs); ps <- permute(ys))
        yield y :: ps
  }

  def keyedPairings[A, B, K](
      as: List[A],
      bs: List[B],
      ka: A => K,
      kb: B => K,
      prio: (K, K) => Boolean
  ) = {
    val ak = as.zipWithIndex groupBy { case (a, i) =>
      ka(a)
    } // need to keep track of permutation
    val bk = bs.zipWithIndex groupBy { case (b, i) => kb(b) }
    val ks = ak.keys ++ bk.keys
    val qs = ks.toList.distinct sortWith prio
    qs map { q => (ak(q), bk(q)) }
  }
}

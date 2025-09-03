package cuvee.util

object Alpha {
  trait term[E, V <: E] {
    this: E =>
    def free: Set[V]
    def rename(re: Map[V, V]): E
    def subst(su: Map[V, E]): E

    def subst(v: V, e: E): E = {
      val su = Map(v -> e)
      subst(su)
    }
  }

  trait x[E, V <: E] extends term[E, V] {
    this: V =>
    def fresh(index: Int): V
    def free = Set(this)
    def rename(re: Map[V, V]) = re.getOrElse(this, this)
    def subst(su: Map[V, E]) = su.getOrElse(this, this)
  }
}

trait Alpha[E <: Alpha.term[E, V], V <: E with Alpha.x[E, V]] {
  context =>

  type term = Alpha.term[E, V]
  type x = Alpha.x[E, V]

  trait bind[A] {
    def bound: Set[V]

    def rename(a: Map[V, V], re: Map[V, V]): A with bind[A]
    def subst(a: Map[V, V], su: Map[V, E]): A with bind[A]

    def avoid(xs: Iterable[V]) = {
      val captured = xs filter bound
      context.fresh(captured)
    }

    def refresh(xs: Iterable[V]) = {
      val alpha = avoid(xs)
      rename(alpha, alpha)
    }

    def rename(re: Map[V, V]): A = {
      val xs = context.free(re)
      val alpha = avoid(xs)
      rename(alpha, re -- bound ++ alpha)
    }

    def subst(su: Map[V, E]): A = {
      val xs = context.free(su)
      val alpha = avoid(xs)
      subst(alpha, su -- bound ++ alpha)
    }
  }

  trait bind2[A] {
    def bound: Set[V]

    def rename(a: Map[V, V], re: Map[V, V], are: Map[V, V]): A with bind2[A]
    def subst(a: Map[V, V], su: Map[V, E], asu: Map[V, E]): A with bind2[A]

    def avoid(xs: Iterable[V]) = {
      val captured = xs filter bound
      context.fresh(captured)
    }

    def refresh(xs: Iterable[V]) = {
      val alpha = avoid(xs)
      rename(alpha, Map(), alpha)
    }

    def rename(re: Map[V, V]): A = {
      val xs = context.free(re)
      val alpha = avoid(xs)
      rename(alpha, re, re -- bound ++ alpha)
    }

    def subst(su: Map[V, E]): A = {
      val xs = context.free(su)
      val alpha = avoid(xs)
      subst(alpha, su, su -- bound ++ alpha)
    }
  }

  class xs(xs: List[V]) {
    def rename(re: Map[V, V]) = xs map (_ rename re)
  }

  class terms(es: List[E]) {
    def free = Set(es flatMap (_.free): _*)
    def rename(re: Map[V, V]) = es map (_ rename re)
    def subst(su: Map[V, E]) = es map (_ subst su)
  }

  var _index = 0

  def resetIndex() = {
    _index = 0
  }

  def nextIndex = {
    _index += 1
    _index
  }

  def id(xs: Iterable[V]): Map[V, V] = {
    val ys = xs map (x => (x, x))
    ys.toMap
  }

  def fresh(x: V) = {
    x fresh nextIndex
  }

  def fresh(xs: Iterable[V]): Map[V, V] = {
    val ys = xs map (x => (x, x fresh nextIndex))
    ys.toMap
  }

  def free(es: Iterable[E]): Set[V] = {
    val ys = es flatMap (_.free)
    ys.toSet
  }

  def free(xs: Map[V, E]): Set[V] = {
    val ys = xs.values flatMap (_.free)
    ys.toSet
  }

  def subst[B <: E](xs: (V, B)*): Map[V, B] = {
    xs.toMap
  }

  def subst[B <: E](xs: Iterable[(V, B)]): Map[V, B] = {
    xs.toMap
  }

  def subst[B <: E](xs: Iterable[V], ys: Iterable[B]): Map[V, B] = {
    require(xs.size == ys.size, "length mismatch")
    val zs = (xs zip ys)
    zs.toMap
  }

  def compose(inner: Map[V, E], outer: Map[V, E]) = {
    val updated = inner map { case (x, e) =>
      (x, e subst outer)
    }
    updated ++ outer
  }

  def alpha[B >: V <: E](bound: Iterable[V], su: Map[V, B]) = {
    val avoid = free(su)
    val captured = bound filter avoid
    val a = context.fresh(captured)
    val su_ = su -- bound ++ a
    (a, su_)
  }
}

import scala.annotation.tailrec

package object cuvee {
  def fail(msg: => String) = {
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
  }

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }

    def intersects(that: Set[A]) = {
      (self & that).nonEmpty
    }
  }

  @tailrec
  def fix[A](f: Set[A] => Set[A], as: Set[A] = Set.empty[A]): Set[A] = {
    val as_ = f(as)
    if (as == as_) as
    else fix(f, as_)
  }
}

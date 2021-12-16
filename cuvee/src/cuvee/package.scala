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
      case None => self
      case Some(index) => this __ index
    }
  }
}

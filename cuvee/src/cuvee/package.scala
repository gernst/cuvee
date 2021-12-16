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

}

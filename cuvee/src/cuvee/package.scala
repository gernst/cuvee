package object cuvee {
  def fail(msg: => String) = {
    require(false, msg)
    ???
  }
}

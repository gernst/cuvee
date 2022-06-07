package cuvee.util

trait Counter {
  var value = 0

  def next = {
    value += 1
    value
  }
}

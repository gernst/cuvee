package cuvee

object Compare {
  def open(path: String) = {
    val source = 
      if (path endsWith ".bpl") {
      boogie.source(path)
    } else if (path endsWith ".smt2") {
      smtlib.source(path)
    } else if (path endsWith ".th") {
      thesy.source(path)
    } else {
      error("unknown file format: " + path)
    }
  }

  def main(args: Array[String]) {
    val (a, b) = args match {
      case Array(a, b) => (a, b)
      case _           => error("comparing lemmas requires two files as arguments")
    }
  }
}

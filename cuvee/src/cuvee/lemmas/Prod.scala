package cuvee.lemmas

object Prod {
  def main(args: Array[String]) {
    val path =
      "/home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/prod/"

    for (i <- 1 to 50) try {
      val name = "prop_%02d".format(i)
      println(name)
      Test(path + name + ".smt2")
    } catch {
      case e: Throwable =>
        println("failed: " + e)
    }
  }
}

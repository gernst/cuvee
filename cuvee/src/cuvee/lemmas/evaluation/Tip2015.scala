package cuvee.lemmas.evaluation

import java.io.File

// BUGGY: /home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/tip2015/nat_le_ge_eq.smt2
object Tip2015 {
  def main(args: Array[String]) {
    val path =
      "/home/ernst/Projects/refinement/tip/benchmarks/benchmarks-smtlib/tip2015/"

    val dir = new File(path)
    for (name <- dir.list if name.endsWith(".smt2")) try {
      Test(path + name)
    } catch {
      case e: Throwable =>
        println("failed: " + e)
    }
  }
}

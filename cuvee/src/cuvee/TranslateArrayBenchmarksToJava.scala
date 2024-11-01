package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.util.Main
import java.io.File
import cuvee.util.Run
import cuvee.c.Translate

object stuff
    extends Run(
      TranslateArrayBenchmarksToJava,
      "../sv-benchmarks/c/array-examples",
      "../sv-benchmarks/c/array-industry-pattern",
      "../sv-benchmarks/c/reducercommutativity",
      "../sv-benchmarks/c/array-tiling",
      "../sv-benchmarks/c/array-programs",
      "../sv-benchmarks/c/array-crafted",
      "../sv-benchmarks/c/array-multidimensional",
      "../sv-benchmarks/c/array-patterns",
      "../sv-benchmarks/c/array-cav19",
      "../sv-benchmarks/c/array-lopstr16",
      "../sv-benchmarks/c/array-fpi"
    )

object TranslateArrayBenchmarksToJava extends Main {
  def main(args: Array[String]) {
    Translate.split = true

    for (path <- args)
      translate(path)
  }

  def translate(path: String) {
    val dir = new File(path)
    for (file <- dir.list() if file endsWith ".yml") {
      val dst = "examples/java/sv-benchmarks/" + file.dropRight(4) + ".java"
      val args = Array(path + "/" + file, "-o", dst)
      println(args.mkString("./Cuvee.sh ", " ", ""))

      try {
        Cuvee.main(args)
      } catch {
        case e: Exception =>
          println("failed: " + e.getMessage())
      }
    }
  }
}

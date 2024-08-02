package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.util.Main
import java.io.File
import cuvee.util.Run

object arrays
    extends Run(
      TranslateArrayBenchmarks,
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

object TranslateArrayBenchmarks extends Main {
  def main(args: Array[String]) {
    for (path <- args)
      translate(path)
  }

  def translate(path: String) {
    val dir = new File(path)
    for (file <- dir.list() if file endsWith ".yml") {
      val dst = "examples/boogie/sv-benchmarks/" + file.dropRight(4) + ".bpl"
      val args = Array(path + "/" + file, "-o", dst)
      println(args.mkString("./Cuvee.sh ", " ", ""))
      
      try {
        Cuvee.main(args)
      } catch {
        case _: Exception =>
          println("failed")
      }
    }
  }
}

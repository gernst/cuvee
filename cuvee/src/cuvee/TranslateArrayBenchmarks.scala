package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr
import java.io.PrintStream
import java.io.FileOutputStream
import cuvee.util.Main
import java.io.File
import cuvee.util.Run

object loops
    extends Run(
      TranslateArrayBenchmarks("examples/boogie/sv-benchmarks/loop"),
      "../sv-benchmarks/c/loops",
      "../sv-benchmarks/c/loop-acceleration",
      "../sv-benchmarks/c/loop-crafted",
      "../sv-benchmarks/c/loop-invgen",
      "../sv-benchmarks/c/loop-lit",
      "../sv-benchmarks/c/loop-new",
      "../sv-benchmarks/c/loop-industry-pattern",
      "../sv-benchmarks/c/loops-crafted-1",
      "../sv-benchmarks/c/loop-invariants",
      "../sv-benchmarks/c/loop-simple",
      "../sv-benchmarks/c/loop-zilu",
      "../sv-benchmarks/c/verifythis",
      "../sv-benchmarks/c/nla-digbench",
      "../sv-benchmarks/c/nla-digbench-scaling"
    )

object arrays
    extends Run(
      TranslateArrayBenchmarks("examples/boogie/sv-benchmarks/array"),
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

case class TranslateArrayBenchmarks(dest: String) extends Main {
  cuvee.c.yml.onlySafe = true

  def main(args: Array[String]) {
    for (path <- args)
      translate(path)
  }

  def translate(path: String) {
    val dir = new File(path)
    for (file <- dir.list() if file endsWith ".yml") {
      val dst = dest + "/" + file.dropRight(4) + ".bpl"
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

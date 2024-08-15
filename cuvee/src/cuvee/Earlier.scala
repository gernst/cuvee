package cuvee

import cuvee.util.Main
import cuvee.util.Run
import java.io.File
import cuvee.smtlib.Res
import java.io.PrintWriter

object tasks
    extends Run(
      Earlier,
      "examples/boogie/sv-benchmarks"
    )

object Earlier extends Main {
  def main(args: Array[String]) {
    for (path <- args) eval(path)
  }

  def eval(path: String) {
    val dir = new File(path)
    for (file <- dir.list() if file endsWith ".bpl") {
      val dst = "evaluation/earlier/sv-benchmarks/" + file.dropRight(4) + ".bpl"
      val args = Array(
        path + "/" + file,
        "-annotate:arrays",
        "-vcgen:partial",
        "-prove:z3",
        "-fail",
        "-o",
        dst
      )
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

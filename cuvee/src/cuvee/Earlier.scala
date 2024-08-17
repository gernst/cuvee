package cuvee

import cuvee.util.Main
import cuvee.util.Run
import cuvee.smtlib.Res
import cuvee.smtlib.Success
import cuvee.smtlib.Unknown
import cuvee.smtlib.Unsupported
import java.io.File
import java.io.PrintStream
import java.io.FileOutputStream

object tasks
    extends Run(
      Earlier,
      // "examples/chc/maxpranq/bench_precondn/c_serialized"
      "examples/boogie/sv-benchmarks"
    )

object Earlier extends Main {
  val dst = "evaluation/earlier/sv-benchmarks/"

  def main(args: Array[String]) {
    for (path <- args) {
      val results = eval(path)
      record(results)
    }
  }

  def eval(path: String): Map[String, Res] = {
    val dir = new File(path)
    val results = for (file <- dir.list() if file endsWith ".bpl") yield {
      // Use either -o or -prove:strict it does not make sense to print only
      // empty files (Unknown, Unsupported) and the c#heap stuff (Success)
      val args = Array(
        path + "/" + file,
        "-annotate:arrays",
        "-vcgen:partial",
        "-prove:z3",
        // "-o",
        // dst + name + ".bpl"
        "-prove:strict"
      )
      file -> eval(args)
    }
    results.toMap
  }

  def eval(task: Array[String]): Res = {
    println(task.mkString("./Cuvee.sh ", " ", ""))
    try {
      Cuvee.main(task)
      Success
    } catch {
      case e: IllegalArgumentException =>
        println(e.getMessage())
        e.getMessage() match {
          case "requirement failed: Could not prove all goals." =>
            Unknown
          case _ =>
            Unsupported
        }
      case e: Exception =>
        println("failed: " + e.getMessage())
        Unsupported
    }
  }

  def record(results: Map[String, Res]) {
    val csv = new PrintStream(new FileOutputStream(dst + "results.csv"))
    csv.println("Name, Result")
    for ((name, result) <- results) csv.println(s"${name}, ${result}")
    csv.close()

    val tex = new PrintStream(new FileOutputStream(dst + "results.tex"))
    val success = results.values.count(x => x == Success)
    tex.println("\\newcommand{\\Success}{" + success + "}")
    val unknown = results.values.count(x => x == Unknown)
    tex.println("\\newcommand{\\Unknown}{" + unknown + "}")
    val unsupported = results.values.count(x => x == Unsupported)
    tex.println("\\newcommand{\\Unsupported}{" + unsupported + "}")
    tex.close()
  }
}

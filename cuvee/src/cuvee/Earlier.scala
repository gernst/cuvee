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
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "examples/boogie/sv-benchmarks",
      // "detailed"
    )

object Earlier extends Main {
  val dst = "evaluation/earlier/"

  def main(args: Array[String]) {
    var detailed = false
    var paths = args
    if (args.last == "detailed") {
      paths = paths.dropRight(1)
      detailed = true
    }

    for (path <- paths) {
      val results = eval(detailed, path)
      if (!detailed) record(path, results)
    }
  }

  def eval(detailed: Boolean, path: String): Map[String, Res] = {
    val dir = new File(path)
    var (dst_, typ) = (dst, "")
    val path_ = path.split("/")
    if (path_.contains("sv-benchmarks")) {
      dst_ += "sv-benchmarks/"
      typ = ".bpl"
    } else if (path_.contains("maxpranq")) {
      dst_ += "maxpranq/"
      typ = ".c"
    } else {
      return Map()
    }

    val results = for (file <- dir.list() if file endsWith typ) yield {
      var args = List(
        path + "/" + file,
        "-annotate:arrays",
        "-vcgen:partial",
        "-prove:z3"
      )

      val file_ = file.substring(0, file.lastIndexOf('.'))

      if (detailed) {
        args = args ++ List("-o", dst_ + file_ + ".bpl")
      } else {
        args = args :+ "-prove:strict"
      }

      file -> eval(args.toArray)
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

  def record(path: String, results: Map[String, Res]) {
    val file = path.replace("/", "_")
    val csv = new PrintStream(new FileOutputStream(dst + file + ".csv"))
    csv.println("Name, Result")
    for ((name, result) <- results) csv.println(s"${name}, ${result}")
    csv.close()

    val tex = new PrintStream(new FileOutputStream(dst + file + ".tex"))
    val success = results.values.count(x => x == Success)
    tex.println("\\newcommand{\\Success}{" + success + "}")
    val unknown = results.values.count(x => x == Unknown)
    tex.println("\\newcommand{\\Unknown}{" + unknown + "}")
    val unsupported = results.values.count(x => x == Unsupported)
    tex.println("\\newcommand{\\Unsupported}{" + unsupported + "}")
    tex.close()
  }
}

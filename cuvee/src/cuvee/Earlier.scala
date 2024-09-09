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

object annotate
    extends Run(
      Earlier(mode = "annotate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "examples/boogie/rapid",
      "examples/boogie/sv-benchmarks"
    )

object reduce
    extends Run(
      Earlier(mode = "reduce"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "examples/boogie/rapid",
      "examples/boogie/sv-benchmarks"
    )

object evaluate
    extends Run(
      Earlier(mode = "evaluate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "examples/boogie/rapid",
      "examples/boogie/sv-benchmarks"
    )

object evaluate_maxpranq
    extends Run(Earlier(mode = "evaluate"), "examples/chc/maxpranq/bench_precondn/c_serialized")
object evaluate_rapid extends Run(Earlier(mode = "evaluate"), "examples/boogie/rapid")
object evaluate_sv_benchmarks
    extends Run(Earlier(mode = "evaluate"), "examples/boogie/sv-benchmarks")

case class Earlier(mode: String) extends Main {
  val dst = "evaluation/earlier/"

  def main(args: Array[String]) {
    for (path <- args) {
      val results = eval(path)
      if (mode == "evaluate") record(path, results)
    }
  }

  def eval(path: String): Map[String, Res] = {
    val dir = new File(path)
    var (dst_, typ) = (dst, "")
    val path_ = path.split("/")
    if (path_.contains("sv-benchmarks")) {
      dst_ += "sv-benchmarks/"
      typ = ".bpl"
    } else if (path_.contains("rapid")) {
      dst_ += "rapid/"
      typ = ".bpl"
    } else if (path_.contains("maxpranq")) {
      dst_ += "maxpranq/"
      typ = ".c"
    } else {
      return Map()
    }

    val results = for (file <- dir.list() if (file endsWith typ)) yield {
      val file_ = file.substring(0, file.lastIndexOf('.'))

      mode match {
        case "annotate" =>
          var args = List(
            path + "/" + file,
            "-annotate:new-arrays",
            // "-vcgen:partial", DO NOT VCGEN THIS
            "-o",
            dst_ + file_ + ".annotated.bpl"
          )

          file -> eval(args.toArray)

        case "reduce" =>
          var args = List(
            path + "/" + file,
            "-annotate:new-arrays",
            "-vcgen:partial",
            "-prove:simple",
            "-split",
            "-o",
            dst_ + file_ + ".reduced.bpl"
          )

          file -> eval(args.toArray)

        case "evaluate" =>
          var args = List(
            path + "/" + file,
            "-annotate:new-arrays",
            "-vcgen:partial",
            "-prove:simple",
            "-prove:crosscheck",
            "-prove:strict"
          )

          file -> eval(args.toArray)
      }
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

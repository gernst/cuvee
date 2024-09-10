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
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

object annotate
    extends Run(
      Earlier(mode = "annotate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

object reduce
    extends Run(
      Earlier(mode = "reduce"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

object evaluate
    extends Run(
      Earlier(mode = "evaluate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

object evaluate_maxpranq
    extends Run(
      Earlier(mode = "evaluate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized"
    )
object evaluate_rapid
    extends Run(Earlier(mode = "evaluate"), "evaluation/earlier/rapid")
object evaluate_sv_benchmarks
    extends Run(Earlier(mode = "evaluate"), "examples/boogie/sv-benchmarks")

object table_rapid
    extends Run(Earlier(mode = "table"), "evaluation/earlier/rapid")

case class Earlier(mode: String) extends Main {
  val dst = "evaluation/earlier/"

  def main(args: Array[String]) {
    for (path <- args) {
      if (mode == "table") {
        table(path)
      } else {
        val results = eval(path)
        if (mode == "evaluate") record(path, results)
      }
    }
  }

  def eval(path: String): Array[(String, Res)] = {
    val dir = new File(path)
    var (dst_, typ) = destinations(path, dir)
    if (typ == "") return Array()

    val results =
      for (
        file <- dir.list().sorted if (file endsWith typ)
          && !(file contains ".annotated.") && !(file contains ".reduced.")
      ) yield {
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
    results
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

  def table(path: String) {
    val dir = new File(path)
    var (dst_, typ) = destinations(path, dir)

    val results =
      for (
        file <- dir.list().sorted if (file endsWith typ)
          && !(file contains ".annotated.") && !(file contains ".reduced.")
      ) yield {
        val file_ = file.substring(0, file.lastIndexOf('.'))

        var args = Array(
          path + "/" + file,
          "-annotate:new-arrays",
          "-vcgen:partial",
          "-prove:simple",
          "-split"
        )

        file -> collect(args)
      }

    val file = path.replace("/", "_")
    val csv = new PrintStream(new FileOutputStream(dst + file + ".table.csv"))
    csv.println(
      "name, result, ensures/assert, " +
        "invariant entry, invariant forward, summary backward, decreases"
    )

    for ((name, result) <- results) {
      var (ens, ien, ifo, sba, dec) = (0, 0, 0, 0, 0)
      for (cmd <- result) {
        cmd match {
          case Lemma(_, _, _, List((_, Some(sexpr.Id(named))))) =>
            if (named == "ensures" || named == "assert")
              ens += 1
            if (named == "invariant entry")
              ien += 1
            if (named == "invariant forward")
              ifo += 1
            if (named == "summary backward")
              sba += 1
            if (named == "decreases")
              dec += 1
          case _ =>
        }
      }
      val res = if (result.isEmpty) Success else Unknown
      csv.println(s"${name}, ${res}, ${ens}, ${ien}, ${ifo}, ${sba}, ${dec}")
    }
  }

  def collect(task: Array[String]) = {
    println(task.mkString("./Cuvee.sh ", " ", ""))
    try {
      Cuvee.collect(task)
    } catch {
      case e: IllegalArgumentException =>
        println(e.getMessage())
        List()
      case e: Exception =>
        println("failed: " + e.getMessage())
        List()
    }
  }

  def record(path: String, results: Array[(String, Res)]) {
    val file = path.replace("/", "_")
    val csv = new PrintStream(new FileOutputStream(dst + file + ".csv"))
    csv.println("Name, Result")
    for ((name, result) <- results) csv.println(s"${name}, ${result}")
    csv.close()

    val tex = new PrintStream(new FileOutputStream(dst + file + ".tex"))
    val success = results.count(x => x._2 == Success)
    tex.println("\\newcommand{\\Success}{" + success + "}")
    val unknown = results.count(x => x._2 == Unknown)
    tex.println("\\newcommand{\\Unknown}{" + unknown + "}")
    val unsupported = results.count(x => x._2 == Unsupported)
    tex.println("\\newcommand{\\Unsupported}{" + unsupported + "}")
    tex.close()
  }

  def destinations(path: String, dir: File) = {
    var dst_ = dst
    path.split("/") match {
      case p if p.contains("sv-benchmarks") =>
        (dst_ + "sv-benchmarks/", ".bpl")

      case p if p.contains("rapid") =>
        (dst_ + "rapid/", ".bpl")

      case p if p.contains("maxpranq") =>
        (dst_ + "maxpranq/", ".c")

      case _ =>
        ("", "")
    }
  }
}

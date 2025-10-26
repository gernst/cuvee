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
import cuvee.smtlib.Goal

object annotate
    extends Run(
      TEQs(mode = "annotate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

object reduce
    extends Run(
      TEQs(mode = "reduce"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

object evaluate
    extends Run(
      TEQs(mode = "evaluate"),
      "examples/chc/maxpranq/bench_precondn/c_serialized",
      "evaluation/earlier/rapid",
      "examples/boogie/sv-benchmarks"
    )

case class TEQs(mode: String) extends Main {
  val dst = "evaluation/teqs/"

  def main(args: Array[String]) {
    for (path <- args) {
      if (mode == "reduce") {
        table(path)
      } else {
        val results = eval(path)
        if (mode == "evaluate") record(path, results)
      }
    }
  }

  def eval(path: String): Array[(String, (Res, Option[String]))] = {
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
            var args = Array(
              path + "/" + file,
              "-annotate:traces",
              // "-vcgen:partial", DO NOT VCGEN THIS
              "-o",
              dst_ + file_ + ".annotated.bpl"
            )

            file -> eval(args)

          case "evaluate" =>
            var args = Array(
              path + "/" + file,
              "-annotate:traces",
              "-vcgen:partial",
              "-split",
              "-simplify2",
              "-prove:z3"
            )

            file -> eval(args)
        }
      }
    results
  }

  def eval(task: Array[String]): (Res, Option[String]) = {
    println(task.mkString("./Cuvee.sh ", " ", ""))
    try {
      Cuvee.main(task)
      (Success, None)
    } catch {
      case e: IllegalArgumentException =>
        println(e.getMessage())
        e.getMessage() match {
          case "requirement failed: Could not prove all goals." =>
            (Unknown, None)
          case _ =>
            (Unsupported, Some(e.getMessage()))
        }
      case e: Exception =>
        println("failed: " + e.getMessage())
        (Unsupported, Some(e.getMessage()))
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
          "-annotate:traces",
          "-vcgen:partial",
          "-split",
          "-simplify2",
          "-o",
          dst_ + file_ + ".reduced.bpl"
        )

        file -> collect(args)
      }

    val file = path.replace("/", "_")
    val csv = new PrintStream(new FileOutputStream(dst + file + ".table.csv"))
    csv.println(
      "name, goal"
    )

    for ((name, result) <- results) {
      val solved = for (cmd <- result) yield cmd match {
        case Lemma(_, _, Some(Goal), _) =>
          false
        case _ =>
          true
      }
      val res = if (solved.forall(b => b)) Success else Unknown
      csv.println(s"${name}, ${res}")
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

  def record(path: String, results: Array[(String, (Res, Option[String]))]) {
    val file = path.replace("/", "_")
    val csv = new PrintStream(new FileOutputStream(dst + file + ".csv"))
    csv.println("Name, Result, Error")
    for ((name, (result, error)) <- results) {
      error match {
        case None        => csv.println(s"${name}, ${result},")
        case Some(value) => csv.println(s"${name}, ${result}, ${value}")
      }
    }
    csv.close()

    val tex = new PrintStream(new FileOutputStream(dst + file + ".tex"))
    val success = results.count(x => x._2._1 == Success)
    tex.println("\\newcommand{\\Success}{" + success + "}")
    val unknown = results.count(x => x._2._1 == Unknown)
    tex.println("\\newcommand{\\Unknown}{" + unknown + "}")
    val unsupported = results.count(x => x._2._1 == Unsupported)
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

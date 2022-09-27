package cuvee.util

import java.io.PrintStream
import java.io.BufferedReader
import java.io.InputStreamReader

object Tool {
  def run(cmd: String*) = {
    val process = new ProcessBuilder(cmd: _*)
    val status = process.start.waitFor()
    status
  }

  def pipe(cmd: String*) = {
    println("$ " + cmd.mkString(" "))
    val builder = new ProcessBuilder(cmd: _*)
    val proc = builder.start()
    val in = new PrintStream(proc.getOutputStream())
    val out = new BufferedReader(new InputStreamReader(proc.getInputStream()))
    val err = proc.getErrorStream()
    (in, out, err, proc)
  }

  import scala.concurrent.ExecutionContext.Implicits.global
  import scala.concurrent._
  import scala.concurrent.duration._
  import scala.util.Try

  def withTimeout[A](ms: Long)(a: => A) = {
    Try(Await.result(Future(a), ms.milliseconds)).toOption
  }

  def withTimeout[A](ms: Long, default: => A)(a: => A) = {
    Try(Await.result(Future(a), ms.milliseconds)).getOrElse(default)
  }
}

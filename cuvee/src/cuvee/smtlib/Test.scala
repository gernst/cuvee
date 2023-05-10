package cuvee.smtlib

import cuvee.util.Main
import cuvee.State
import cuvee.pure._
import cuvee.sexpr
import java.io.FileReader
import cuvee.util.Run
import java.io.StringReader
import cuvee.backend.Sink

object Test extends Main {
  def foo(args: Array[String]) {
    for (file <- args) {
      val st = State.default
      val a = sexpr.parse(file)
      val q = new Parser(st)
      val c = q.cmds(a)
      for (x <- c)
        println(x)
    }
  }

  def main(args: Array[String]): Unit = {
    val st = State.default
    val solver = z3(st)

    val cmds = List(
      SetOption("produce-models", "true"),
      DeclareFun("x", Nil, Nil, Sort.int),
      CheckSat
    )

    for (cmd <- cmds) {
      val res = solver.exec(cmd)
      println(res)
    }
  }
}

object r1 extends Run(Test, "examples/1.smt2")

object list_defs extends Run(Test, "examples/list-defs.smt2")

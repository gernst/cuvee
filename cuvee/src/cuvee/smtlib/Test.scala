package cuvee.smtlib

import cuvee.util.Main
import cuvee.pure.State
import cuvee.sexpr
import java.io.FileReader
import cuvee.util.Run

object Test extends Main {
  def main(args: Array[String]): Unit = {
    for (file <- args) {
      val st = State.default
      val a = sexpr.parse(file)
      val q = new Parser(st)
      val c = q.cmds(a)
      for (x <- c)
        println(x)
    }
  }
}

object r1 extends Run(Test, "examples/1.smt2")

object list_defs extends Run(Test, "examples/list-defs.smt2")

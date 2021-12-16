package cuvee.smtlib

import cuvee.util.Main
import cuvee.pure.State
import cuvee.sexpr
import java.io.FileReader
import cuvee.util.Run

object Test extends Main {
  def main(args: Array[String]): Unit = {
    for (f <- args) {
      println(f)
      val st = State.default

      val r = new FileReader(f)
      val s = new sexpr.Scanner(r)
      val p = new sexpr.Parser(s)
      val a = p.sexprs()
      val q = new Parser(st)
      val c = q.cmds(a)
      for (x <- c)
        println(x)
    }
  }
}

object r1 extends Run(Test, "examples/1.smt2")

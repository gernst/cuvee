package cuvee.test

import cuvee._
import minitest.SimpleTestSuite
import java.io.File
import scala.concurrent.ExecutionContext

object Examples extends TestSuite {
  val dir = "examples"

  val tests = List(
    "add.smt2",
    "gcd.smt2",
    "map.smt2",
    "max.smt2",
    "loop.smt2",
    "compare.smt2")

  for (file <- tests if file.endsWith(".smt2")) {
    val path = dir + "/" + file

    val in = new File(path)
    val source = Source.file(in)
    val report = prove_!

    test(path + " (z3)") {
      withSolver(Solver.z3(), solver =>
        Cuvee.run(source, solver, report))
    }

    test(path + " (cvc4)") {
      withSolver(Solver.cvc4(), solver =>
        Cuvee.run(source, solver, report))
    }
  }

  def main(args: Array[String]) {
    implicit val ec: ExecutionContext = scala.concurrent.ExecutionContext.global

    for (property <- properties) {
      val future = property(())
      for (result <- future) {
        print(result.formatted(property.name, false))
      }
    }
  }
}
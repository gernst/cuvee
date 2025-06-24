package cuvee.test

import cuvee.Cuvee
import minitest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.pure.Simplify
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Success
import cuvee.smtlib.Unknown
import cuvee.smtlib.Unsupported

object Verify extends SimpleTestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  val stream = new ByteArrayOutputStream
  System.setOut(new java.io.PrintStream(stream))

  test("annotated") {
    val annotated = new File(testResources, "annotated")
    val files = find(testResources, ".bpl", exclude = List("simplify"))

    for (file <- annotated.listFiles()) {
      val task = file.toString
      val args = Array("-vcgen:partial", "-split", "-z3", task)

        Cuvee.main(args)
    }
  }
}

package cuvee.test

import cuvee.Cuvee
import utest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.pure.Simplify
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Success
import cuvee.smtlib.Unknown
import cuvee.smtlib.Unsupported

object Verify extends TestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  val stream = new ByteArrayOutputStream
  System.setOut(new java.io.PrintStream(stream))

  val tests = Tests {
    test("annotated") {
      val annotated = new File(testResources, "annotated")

      for (file <- annotated.listFiles()) {
        val task = file.toString
        val cmds = Array("-vcgen:partial", "-split", "-z3", task)

        val result = eval(cmds)

        assert(result == Success)
      }
    }
  }

  def eval(task: Array[String]) = {
    try {
      Cuvee.main(task)
      Success
    } catch {
      case e: IllegalArgumentException =>
        e.getMessage() match {
          case "requirement failed: Could not prove all goals." => Unknown
          case _                                                => Unsupported
        }
      case e: Exception => Unsupported
    }
  }
}

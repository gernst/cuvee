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
  val exclude = List("simplify", "induction")

  val tests = Tests {
    test("annotated") {
      val annotated = new File(testResources, "annotated")
      val files = find(annotated, ".bpl", exclude)
      for (file <- files){
        val task = file.toString
        val cmds = Array("-vcgen:partial", "-split", "-z3", task)
        Cuvee.main(cmds)
      }
    }
    
    test("induction") {
      val induction = new File(testResources, "induction")
      val files = find(induction, ".bpl", exclude)
      for (file <- files){
        val task = file.toString
        val cmds = Array("-prove:z3", "-z3", task)
        Cuvee.main(cmds)
      }
    }
  }
}

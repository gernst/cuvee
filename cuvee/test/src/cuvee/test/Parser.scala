package cuvee.test

import cuvee.Cuvee
import utest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.smtlib.DefineProc
import cuvee.pure.Simplify
import cuvee.ListOps

object Parser extends TestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  val tests = Tests {
    test("parser") {
      val files = find(testResources, ".bpl", exclude = List("simplify", "induction"))

      for (file <- files) {
        val task = file.toString
        val tmpFile = File.createTempFile("tmp-" + task, ".bpl")
        tmpFile.deleteOnExit()

        val stream = new ByteArrayOutputStream
        System.setOut(new java.io.PrintStream(stream))

        val fst = Cuvee.collect(Array(task))
        val fos = new FileOutputStream(tmpFile)
        stream.writeTo(fos);
        stream.close()

        val snd = Cuvee.collect(Array(tmpFile.getAbsolutePath()))
        assert(fst == snd)
      }
    }
  }
}

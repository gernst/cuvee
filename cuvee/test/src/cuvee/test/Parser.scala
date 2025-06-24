package cuvee.test

import cuvee.Cuvee
import minitest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.smtlib.DefineProc
import cuvee.pure.Simplify
import cuvee.ListOps

object Parser extends SimpleTestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  test("parser") {
    val files = find(testResources, ".bpl", exclude = List("simplify"))

    for (file <- files) {
      val task = file.toString
      val tmpFile = File.createTempFile("tmp-" + task, ".bpl")
      tmpFile.deleteOnExit()

      val args = Array(task, "-o", tmpFile.getAbsolutePath())
      val fst = Cuvee.collect(args)
      val fos = new FileOutputStream(tmpFile)

      val snd = Cuvee.collect(Array(tmpFile.getAbsolutePath()))

      assert(fst == snd)
    }
  }
}

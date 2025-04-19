package cuvee.test

import cuvee.Cuvee
import utest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.smtlib.DefineProc
import cuvee.pure.Simplify

object Parser extends TestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  val stream = new ByteArrayOutputStream
  System.setOut(new java.io.PrintStream(stream))

  val tests = Tests {
    test("parser") {
      val files = getAllFiles(testResources, List())
      for (file <- files) {
        val task = file.toString
        val tmpFile = File.createTempFile("tmp-" + task, ".bpl")
        tmpFile.deleteOnExit()

        val fst = Cuvee.collect(Array(task))
        val fos = new FileOutputStream(tmpFile)
        stream.writeTo(fos);

        val snd = Cuvee.collect(Array(tmpFile.getAbsolutePath()))

        // TODO which way? Handle in test or fix in cuvee?
        // cuvee adds "&& true" to the spec, one with each call
        // meaning: they are not syntactically equal
        assert(fst == snd)
      }
    }
  }

  def getAllFiles(current: File, collectFiles: List[File]): List[File] = {
    var allFiles = collectFiles
    for (file <- current.listFiles()) {
      if (file.isDirectory())
        allFiles = allFiles ++ getAllFiles(file, allFiles)
      else
        allFiles = allFiles :+ file
    }
    allFiles
  }
}

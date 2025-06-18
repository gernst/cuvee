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
  val exclude = List("simplify")

  val tests = Tests {
    test("parser") {
      val files = getAllFiles(testResources)

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

  def getAllFiles(current: File): List[File] = {
    var allFiles: List[File] = List()
    for (file <- current.listFiles()) {
      if (file.isDirectory() && !(exclude contains file.getName()))
        allFiles = allFiles ++ getAllFiles(file)
      else if (file.toString.endsWith(".bpl"))
        allFiles = allFiles :+ file
    }
    allFiles
  }
}

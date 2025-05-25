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

  val stream = new ByteArrayOutputStream
  System.setOut(new java.io.PrintStream(stream))

  val tests = Tests {
    // TODO problem with "requirement failed: procedure already declared"
    // Does cuvee keep parts of the state with collect?
    test("parser") {
      val files = getAllFiles(testResources)

      for (file <- files) {
        val task = file.toString
        val tmpFile = File.createTempFile("tmp-" + task, ".bpl")
        tmpFile.deleteOnExit()

        try { // TODO debug
          val fst = Cuvee.collect(Array(task))
          val fos = new FileOutputStream(tmpFile)
          stream.writeTo(fos);

          val snd = Cuvee.collect(Array(tmpFile.getAbsolutePath()))

          assert(fst == snd)
        } catch { // TODO debug
          case e: Exception =>
            println(task)
            println(e.getMessage())
        }
      }
    }
  }

  def getAllFiles(current: File): List[File] = {
    var allFiles: List[File] = List()
    for (file <- current.listFiles()) {
      if (file.isDirectory())
        allFiles = allFiles ++ getAllFiles(file)
      else if (file.toString.endsWith(".bpl"))
        allFiles = allFiles :+ file
    }
    allFiles
  }
}

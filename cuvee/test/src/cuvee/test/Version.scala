package cuvee.test

import utest._
// import java.io.ByteArrayOutputStream

import cuvee.Cuvee
import cuvee.Config

object Version extends TestSuite {
  // val stream = new java.io.PrintStream(new ByteArrayOutputStream)
  // System.setOut(stream)
  val tests = Tests {
    test("version") {
      test("level2") {
        Cuvee("examples/boogie/add.bpl")
      }
    }
  }
}

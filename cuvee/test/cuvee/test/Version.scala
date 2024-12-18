package cuvee.test

import utest._
import java.io.StringWriter

import cuvee.Cuvee

object Version extends TestSuite {
  System.setOut(???)
  test("version") {
    Cuvee("-version")
  }
}

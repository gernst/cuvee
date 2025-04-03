package cuvee

import utest._
// import java.io.StringWriter

import cuvee.Cuvee
import cuvee.Config

object Version extends TestSuite {
  // Currently useless, not sure if it is even correct
  // val stream = new java.io.PrintStream(new ByteArrayOutputStream)
  // System.setOut(stream)
  val tests = Tests {
    'example1 - {
      throw new Exception("test1")
    }
    'example2 - {
      'level2 - {
        1
      }
    }
    'examples3 - {
      val a = List[Byte](1, 2)
      a(10)
    }
    'version - { // TODO
      // Note the problem is not the name of the test
      // starting with this one the tests are not shown as tests
      // (depending on the position of the `Cuvee` line)
      // The output gets printed
      Cuvee("-version")
      // Cuvee("-help")// this is effective dead code
    }
    // TODO which syntax?
    // Seems to behave the same, including wildcards for names
    // as well as nested tests
    test("version") {
      test("level2") {
        Cuvee("-version")
      }
    }

  }
}

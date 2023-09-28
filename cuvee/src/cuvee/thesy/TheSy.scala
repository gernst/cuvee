package cuvee.thesy

import cuvee.State
import cuvee.pure._
import cuvee.util.Tool
import cuvee.util.Name
import java.io.BufferedReader
import java.io.FileReader
import java.io.StringReader
import cuvee.smtlib.Solver

object TheSy {
  def apply(file: String) {
    val (in, out, err, proc) = Tool.pipe("TheSy", file)

    var line = out.readLine()
    while (line != null) {
      val pos = line.indexOf("proved: ")
      if (pos >= 0) {
        val rest = ???
      }

      line = out.readLine()
    }
  }
}

package cuvee

import java.io.FileReader
import java.util.regex.Pattern
import java.io.Reader

package object sexpr {
  var debug = false

  val True = Id("true")
  val False = Id("false")

  def parse(file: String): List[Expr] = {
    parse(new FileReader(file))
  }

  def parse(reader: Reader): List[Expr] = {
    val scanner = new sexpr.Scanner(reader)
    val parser = new sexpr.Parser(scanner)
    val result = parser.sexprs()
    if(debug)
      println(result)
    result
  }

  def iterator(reader: Reader): Iterator[Expr] = {
    val scanner = new sexpr.Scanner(reader)
    val parser = new sexpr.Parser(scanner)
    parser.iterator
  }

  val simplePattern =
    "[:]?[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*"

  def ok = Pattern.compile(simplePattern)

  def mangle(str: String): String = {
    if (ok.matcher(str).matches()) str
    else "|" + str + "|"
  }
}

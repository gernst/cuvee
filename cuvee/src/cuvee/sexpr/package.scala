package cuvee

import java.io.FileReader
import java.util.regex.Pattern

package object sexpr {
  implicit def toSyntaxList(xs: List[Syntax]) = new SyntaxList(xs: List[Syntax])

  val True = Id("true")
  val False = Id("false")

  def parse(file: String): List[Expr] = {
    val reader = new FileReader(file)
    val scanner = new sexpr.Scanner(reader)
    val parser = new sexpr.Parser(scanner)

    parser.sexprs()
  }

  val simplePattern =
    "[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*"

  def ok = Pattern.compile(simplePattern)

  def mangle(str: String): String = {
    if (ok.matcher(str).matches()) str
    else "|" + str + "|"
  }
}

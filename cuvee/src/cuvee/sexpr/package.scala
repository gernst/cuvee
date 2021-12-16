package cuvee

import java.io.FileReader

package object sexpr {
  def parse(file: String): List[Expr] = {
      val reader = new FileReader(file)
      val scanner = new sexpr.Scanner(reader)
      val parser = new sexpr.Parser(scanner)

      parser.sexprs()
  }
}

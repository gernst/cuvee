package cuvee.python

import fastparse._
import pythonparse.Ast
import cuvee.State

class Parser {
  def parsePython(lines: String): List[Ast.stmt] = {
    val parser: P[_] => P[Any] = pythonparse.Statements.file_input(_)

    parse(lines, parser) match {
      case fastparse.Parsed.Success(value: Seq[Ast.stmt], index) =>
        value.toList
      case fastparse.Parsed.Failure(label, index, extra) =>
        throw new RuntimeException("Parse Error")
    }
  }
}

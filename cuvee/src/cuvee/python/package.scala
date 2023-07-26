package cuvee

import pythonparse.Ast
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Cmd
import cuvee.pure.Datatype
import cuvee.pure.Var
import cuvee.pure.Param
import cuvee.pipe.Source
import java.io.InputStreamReader
import java.io.FileReader
import java.io.Reader
import java.io.BufferedReader

package object python {
  val (prelude, state) = cuvee.boogie.parse("cuvee/src/cuvee/python/python.bpl")

  val a = Param("a")
  val old = state.fun("old", List(a), List(a), a)
  val fin = state.fun("final", List(a), List(a), a)

  def parse(lines: String): List[Ast.stmt] = {
    import fastparse._
    val parser: P[_] => P[Any] = pythonparse.Statements.file_input(_)

    fastparse.parse(lines, parser) match {
      case fastparse.Parsed.Success(value: Seq[Ast.stmt], index) =>
        value.toList
      case fastparse.Parsed.Failure(label, index, extra) =>
        throw new RuntimeException("Parse Error")
    }
  }

  def source(path: String): Source = new Source {
    val source = scala.io.Source.fromFile(path)
    val lines = source.mkString

    val py = parse(lines)

    val sig = new Signature(python.state.copy())
    val exprs = new Exprs(sig)
    val stmts = new Stmts(exprs)

    val it =
      for (
        stmt <- py.iterator;
        cmd <- stmts.createCmd(stmt)
      )
        yield cmd

    def state = python.state
    def next() = it.next()
    def hasNext = it.hasNext
  }
}

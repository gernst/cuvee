package cuvee

import java.io.FileReader
import java.io.File
import java.io.Reader
import cuvee.pipe.Source
import cuvee.smtlib.Cmd

package object c {
  var bits = 32

  def parse(path: String): List[Stmt] = {
    parse(new FileReader(path), path)
  }

  def parse(file: File): List[Stmt] = {
    parse(new FileReader(file), file.getPath)
  }

  def parse(reader: Reader, path: String): List[Stmt] = {
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val types = new java.util.HashSet[String]
    scanner.types = types
    parser.types = types

    val Group(stmts) = parser parse scanner
    stmts
  }

  def source(file: String) = new Source {
    val state = Translate.state.copy()

    val from = {
      val stmts = parse(file)
      val translate = new Translate(state)
      val progs = translate.globals(stmts)
      Translate.prelude.iterator ++ progs.iterator
    }

    def hasNext = from.hasNext
    def next() = from.next()
  }

  object yml {
    def source(path: String) = {
      import java.io.FileInputStream
      import org.yaml.snakeyaml.Yaml

      val yaml = new Yaml()
      val file = new File(path)
      val base = file.getParent()
      val stream = new FileInputStream(file)
      val data = yaml.load[Any](stream).asInstanceOf[java.util.Map[String, Any]]
      val input = base + "/" + data.get("input_files").toString
      c.source(input)
    }
  }
}

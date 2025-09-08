package cuvee

import java.io.FileReader
import java.io.File
import java.io.Reader
import cuvee.pipe.Source
import cuvee.smtlib.Cmd
import cuvee.util.Yaml

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
    def source(path: String, onlySafe: Boolean = false) = {
      val data = Yaml.load(path)

      val file = new File(path)
      val base = file.getParent()
      val input = base + "/" + data("input_files").asString

      if (onlySafe) {
        val properties = data("properties")

        val ok = properties.asList exists { entry =>
          if (entry("property_file").asString == "../properties/unreach-call.prp")
            entry.get("expected_verdict").exists(_.asBoolean)
          else
            false
        }

        require(ok, "discard unsafe benchmark: " + input)
      }

      c.source(input)
    }
  }
}

/* properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true
  - property_file: ../properties/coverage-branches.prp
 */

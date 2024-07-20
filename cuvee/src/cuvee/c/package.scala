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

    val Block(stmts) = parser parse scanner
    stmts
  }


  def source(file: String) = new Source {

    override def state: State = ???

    override def hasNext: Boolean = ???

    override def next(): Cmd = ???

    
  }
    
}

package cuvee

import java.io.Reader
import cuvee.pipe.Source
import java.io.InputStreamReader
import java.io.FileReader

package object thesy {
  def source(): Source = source(new InputStreamReader(System.in))
  def source(path: String): Source = source(new FileReader(path))

  def source(reader: Reader): Source = new Source {
    val from = cuvee.sexpr.iterator(reader)
    val init = State.default
    val parser = new cuvee.thesy.Parser(init)

    def state = parser.st
    def hasNext = from.hasNext
    def next() = parser.cmd(from.next)
  }
}

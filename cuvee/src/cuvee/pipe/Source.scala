package cuvee.pipe

import cuvee.State
import cuvee.smtlib._
import java.io.Reader
import cuvee.util.Name
import cuvee.pure.Param
import cuvee.pure.Var
import java.io.FileReader
import java.io.InputStreamReader

trait Source extends Iterator[Cmd] {
  def hasNext: Boolean
  def next(): Cmd
}

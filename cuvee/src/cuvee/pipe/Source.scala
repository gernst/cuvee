package cuvee.pipe

import cuvee.State
import cuvee.smtlib._
import java.io.Reader
import cuvee.util.Name
import cuvee.pure.Param
import cuvee.pure.Var
import java.io.FileReader
import java.io.InputStreamReader

// the returned state is *after* considering the returned command
trait Source extends Iterator[Cmd] {
  def state: State
  def hasNext: Boolean
  def next(): Cmd
}

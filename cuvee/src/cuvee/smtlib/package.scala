package cuvee

import cuvee.pure.State

package object smtlib {
  def parse(file: String): (List[Cmd], State) = {
    val from = sexpr.parse(file)

    val st = State.default
    val parser = new Parser(st)

    val res = parser.cmds(from)
    (res, parser.st)
  }
}

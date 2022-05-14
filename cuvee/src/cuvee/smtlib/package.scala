package cuvee

import cuvee.pure.State

package object smtlib {
  def parse(file: String): (List[Cmd], State) = {
    val from = sexpr.parse(file)
    val st = State.default
    val res = parse(from, st)
    (res, st)
  }

  def parse(from: List[sexpr.Expr], st: State): List[Cmd] = {
    val parser = new Parser(st)
    val res = parser.cmds(from)
    res
  }
}

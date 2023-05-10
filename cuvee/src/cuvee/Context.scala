package cuvee

import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Name

class Context(init: State, prelude: List[Cmd] = Nil) {
  class Entry(var state: State, var rcmds: List[Cmd])

  var stack = List(new Entry(init, prelude))

  def top = stack.head
  def state = top.state
  def rcmds = top.rcmds
  def cmds = rcmds.reverse

  def push(n: Int) {
    val add = List.tabulate(n)(_ => stack.head)
    stack = add ++ stack
  }

  def pop(n: Int) {
    stack = stack drop n
  }

  def track(cmd: Cmd) = {
    top.rcmds = cmd :: top.rcmds
    cmd
  }

  def fun(name: Name, params: List[Param], args: List[Type], typ: Type) = {
    state.fun(name, params, args, typ)
    track(DeclareFun(name, params, args, typ))
  }
}

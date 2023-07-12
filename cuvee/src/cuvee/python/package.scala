package cuvee

import pythonparse.Ast
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Cmd
import cuvee.pure.Datatype
import cuvee.pure.Var
import cuvee.pure.Param

package object python {
  val (prelude, state) = cuvee.boogie.parse("cuvee/src/cuvee/python/python.bpl")

  val value = state.sort("pyValue")
  val pyNone = state.funs("pyNone", 0)

  val int = state.sort("Int")
  val pyInt = state.funs("pyInt", 1)
  val pyGetInt = state.funs("pyGetInt", 1)

  val bool = state.sort("Bool")
  val pyBool = state.funs("pyBool", 1)
  val pyGetBool = state.funs("pyGetBool", 1)

  val pyIsTrue = state.funs("pyIsTrue", 1)
  val pyTrue = state.funs("pyTrue", 0)
  val pyFalse = state.funs("pyFalse", 0)
  val pyDefaultArray = state.funs("pyDefaultArray", 0)

  val pyArray = state.funs("pyArray", 2)
  val pyGetLength = state.funs("pyGetLength", 1)
  val pyGetArray = state.funs("pyGetValues", 1)

  val a = Param("a")
  val old = state.fun("old", List(a), List(a), a)
  val fin = state.fun("final", List(a), List(a), a)

  val constrs = List(
    (pyNone, Nil),
    (pyInt, List(pyGetInt)),
    (pyBool, List(pyGetBool)),
    (pyArray, List(pyGetArray, pyGetLength))
  )

  val dt = Datatype(Nil, constrs)
  state.datatype("pyValue", dt) // register the datatype

  val pyResult = Var("pyResult", value)

  def parse(file: String): (List[Cmd], List[Cmd], State) = {
    val source = scala.io.Source.fromFile(file)
    val lines =
      try source.mkString
      finally source.close()

    val parser = new Parser()
    val stmts = parser.parsePython(lines)

    /*for (stmt <- stmts) // DEBUG
      println(stmt)
    println()*/

    val cmds: List[Cmd] = createCmds(stmts)

    /*for (cmd <- cmds) // DEBUG
      println(cmd)
    println()*/

    (prelude, cmds, state)
  }

  def createCmds(stmts: Seq[Ast.stmt]): List[Cmd] = stmts match {
    case Nil => List.empty[Cmd]
    case Ast.stmt.ImportFrom(module, _, _) :: next
        if module == Option(Ast.identifier("help_methods")) =>
      createCmds(next)
    case head :: next => getCmd(head) :: createCmds(next)
  }

  def getCmd(stmt: Ast.stmt): Cmd = stmt match {
    case Ast.stmt.FunctionDef(name, args, body, _) =>
      val in = spec.input(args)
      val out = spec.output(body)
      val method = spec.body(body, in)
      val param = List(Param(name.name))
      state.proc(name.name, param, in, out, method._1);
      state.procdef(name.name, in, out, method._2);
      DefineProc(
        name.name,
        in,
        out,
        method._1,
        method._2
      )
    case Ast.stmt.ClassDef(name, bases, body, _) =>
      cuvee.undefined
    case _ => cuvee.undefined
  }
}

package cuvee

import cuvee.pure.State
import java.io.PrintStream
import cuvee.pure.Expr
import cuvee.util.Tool
import cuvee.backend.Solver
import cuvee.backend.Sink
import java.io.BufferedReader

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

  def z3(st: State, timeout: Int = 1000) =
    new solver(st, "z3", "-t:" + timeout, "-in")

  def cvc4(st: State, timeout: Int = 1000) =
    new solver(st, "cvc4", "--tlimit=" + timeout, "--lang=smt2", "--incremental", "--increment-triggers")

  def echo(st: State)
    = new solver(st, "echo", "unsat")

  val PrintSuccess = SetOption(List(":print-success", "true"))

  class solver(st: State, cmd: String*) extends Solver {
    val (out, in, err, proc) = Tool.pipe(cmd: _*)

    val parser = new Parser(st)
    val res = sexpr.iterator(in)

    require(control(PrintSuccess) == Success)

    def write(cmd: Cmd) {
      for (line <- cmd.lines) {
        out.println(line)
      }
      out.flush()
    }

    def read() = {
      val line = res.next()
      line
    }

    def ack(cmd: Cmd): Ack = {
      write(cmd)
      parser.ack(read())
    }

    def check(): IsSat = {
      write(CheckSat)
      parser.issat(read())
    }

    def model(): Model = {
      write(GetModel)
      // parser.model(read())
      ???
    }

    def assertions(): Assertions = {
      write(GetAssertions)
      // parser.assertions(read())
      ???
    }
  }
}

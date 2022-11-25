package cuvee

import cuvee.State
import java.io.PrintStream
import cuvee.pure.Expr
import cuvee.util.Tool
import cuvee.backend.Solver
import cuvee.backend.Sink
import java.io.BufferedReader
import cuvee.sexpr.Printer

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
    new solver(
      st,
      "cvc4",
      "--tlimit-per=" + timeout,
      "--lang=smt2",
      "--incremental",
      "--increment-triggers"
    )

  def cvc5(st: State, timeout: Int = 1000) =
    new solver(
      st,
      "cvc5",
      "--tlimit-per=" + timeout,
      "--lang=smt2",
      "--incremental",
      "--increment-triggers"
    )

  def echo(st: State) = new solver(st, "echo", "unsat")

  val PrintSuccess = SetOption("print-success", "true")

  object stdout extends print(System.out)
  object stderr extends print(System.err)

  class print(out: PrintStream) extends Sink {
    def ack(cmd: Cmd) = {
      for (line <- cmd.lines)
        out println line
      Success
    }

    def check() = {
      for (line <- CheckSat.lines)
        out println line
      Unknown
    }

    def model() = {
      for (line <- GetModel.lines)
        out println line
      Model(Nil, Nil)
    }
  }

  object solver {
    var debug = false
  }

  class solver(st: State, cmd: String*) extends Solver {
    val (out, in, err, proc) = Tool.pipe(cmd: _*)

    val parser = new Parser(st.copy())
    val res = sexpr.iterator(in)

    require(control(PrintSuccess) == Success)

    def write(cmd: Cmd) {
      for (line <- cmd.lines) {
        out.println(line)
        if (solver.debug)
          println("> " + line)
      }
      out.flush()
    }

    def read() = {
      val line = res.next()
      if (solver.debug)
        println("< " + line)
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
      // Note: do not scope parser, may depend on prior SAT results and models
      write(GetModel)
      val (decls, defs) = parser.model(read())
      Model(decls, defs)
    }
  }

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = Printer
}

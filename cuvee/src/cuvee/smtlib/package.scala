package cuvee

import cuvee.State
import java.io.PrintStream
import cuvee.pure.Expr
import cuvee.util.Tool
import cuvee.backend.Solver
import java.io.BufferedReader
import cuvee.sexpr.Printer
import java.io.FileReader
import cuvee.pipe.Source
import java.io.InputStreamReader
import java.io.Reader

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

  def source() : Source = source(new InputStreamReader(System.in))
  def source(path: String): Source  = source(new FileReader(path))

  def source(reader: Reader): Source  = new Source {
    val from = cuvee.sexpr.iterator(reader)
    val init = State.default
    val parser = new cuvee.smtlib.Parser(init)

    def hasNext = from.hasNext
    def next() = parser.cmd(from.next())
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

  val PrintSuccess = SetOption("print-success", "true")

  object solver {
    var debug = false
  }

  class solver(st: State, cmd: String*) extends Solver {
    val (out, in, err, proc) = Tool.pipe(cmd: _*)

    val parser = new Parser(st)
    val res = sexpr.iterator(in)

    require(control(PrintSuccess) == Success)
    
    def destroy() {
      proc.destroy()
    }

    def write(cmd: Cmd) {
      for (line <- cmd.lines) {
        out.println(line)
        if(solver.debug)
          println("> " + line)
      }
      out.flush()
    }

    def read() = {
      val line = res.next()
      if(solver.debug)
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
      write(GetModel)
      Model(parser.model(read()))
    }
  }

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = Printer
}

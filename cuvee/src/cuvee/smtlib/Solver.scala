package cuvee.smtlib

import cuvee.State
import java.io.PrintStream
import java.io.BufferedReader
import java.io.InputStreamReader
import cuvee.pure._
import cuvee.util.Tool
import cuvee.sexpr.Printer
import java.io.FileReader
import cuvee.pipe.Source
import java.io.Reader
import cuvee.pure.True
import cuvee.pipe.Sink
import cuvee.pipe.Stateful

trait Solver extends Sink {
  // unsafe on commands that don't ack
  def ack(cmd: Cmd): Ack

  def check(): IsSat
  def model(): Model

  def exec(cmd: Cmd): Res =
    cmd match {
      case cmd: Ctrl =>
        control(cmd)
      case cmd: Decl =>
        declare(cmd)
      case assert: Assert =>
        ack(assert)
      case CheckSat =>
        check()
      case GetModel =>
        model()
    }

  def control(cmd: Ctrl) =
    ack(cmd)

  def declare(cmd: Decl) =
    ack(cmd)

  def assert(expr: Expr) =
    ack(Assert(expr))

  def assert(exprs: List[Expr]): Any = {
    for (expr <- exprs) assert(expr)
  }

  def push() =
    control(Push(1))

  def pop() =
    control(Pop(1))

  def scoped[A](f: => A) = try {
    push()
    f
  } finally {
    pop()
  }

  def check(phi: Expr): IsSat = scoped {
    assert(phi)
    check()
  }

  def isTrue(phi: Expr) =
    (phi == True) || isUnsat(!phi)

  def isFalse(phi: Expr) =
    (phi == False) || isUnsat(phi)

  def isSat(phi: Expr) = {
    val status = check(phi)
    status == Sat
  }

  def isUnsat(phi: Expr) = {
    val status = check(phi)
    status == Unsat
  }

  def isSat = {
    val status = check()
    status == Sat
  }

  def isUnsat = {
    val status = check()
    status == Unsat
  }
}

object Solver {
  var debug = false

  object dummy extends Solver {
    def ack(cmd: Cmd) = Success
    def check() = Unknown
    def model() = cuvee.error("no model")
  }
  
  def z3(timeout: Int = 1000) =
    new solver("z3", "-t:" + timeout, "-in")

  def cvc4(timeout: Int = 1000) =
    new solver(
      "cvc4",
      "--tlimit-per=" + timeout,
      "--lang=smt2",
      "--incremental",
      "--increment-triggers"
    )
    
  def cvc5(timeout: Int = 1000) =
    new solver(
      "cvc5",
      "--tlimit-per=" + timeout,
      "--lang=smt2",
      "--incremental",
      "--increment-triggers"
    )

  val PrintSuccess = SetOption("print-success", "true")

  class solver(cmd: String*) extends Solver with Stateful {
    val (out, in, err, proc) = Tool.pipe(cmd: _*)

    val parser = new Parser(state)
    val res = cuvee.sexpr.iterator(in)

    require(control(PrintSuccess) == Success)
    
    def destroy() {
      proc.destroy()
    }

    def write(cmd: Cmd) {
      for (line <- cmd.lines) {
        out.println(line)
        if(debug)
          println("> " + line)
      }
      out.flush()
    }

    def read() = {
      val line = res.next()
      if(debug)
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
}

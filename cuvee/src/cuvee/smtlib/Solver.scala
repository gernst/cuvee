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

trait Solver extends Sink {
  // unsafe on commands that don't ack
  def ack(cmd: Cmd): Ack

  def check(): IsSat
  def info(attr: String): Info
  def labels(): Labels
  def model(state: State): Model

  def exec(cmd: Cmd, state: State): Res =
    cmd match {
      case CheckSat =>
        check()
      case Lemma(expr, tactic, assert) =>
        if (assert)
          this.assert(expr)
        else
          Success
      case GetModel =>
        model(state)
      case GetInfo(attr) =>
        info(attr)
      case Labels =>
        labels()
      case cmd =>
        ack(cmd)
    }

  def assert(expr: Expr) =
    ack(Assert(expr))

  def assert(exprs: List[Expr]): Any = {
    for (expr <- exprs)
      assert(expr)
  }

  def push() =
    ack(Push(1))

  def pop() =
    ack(Pop(1))

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
    def done(state: State) {}
    def ack(cmd: Cmd) = Success
    def check() = Unknown
    def info(attr: String) = Error("no such info: " + attr)
    def labels(): Labels = Error("no labels")
    def model(state: State) = Error("no model")
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

  class solver(cmd: String*) extends Solver {
    val (out, in, err, proc) = Tool.pipe(cmd: _*)

    val res = cuvee.sexpr.iterator(in)

    require(ack(PrintSuccess) == Success)

    def done(state: State) {
      destroy()
    }

    def destroy() {
      proc.destroy()
    }

    def write(cmd: Cmd) {
      for (line <- cmd.lines) {
        out.println(line)
        if (debug)
          println(proc.pid + "> " + line)
      }
      out.flush()
    }

    def read() = {
      val line = res.next()
      if (debug)
        println(proc.pid + "< " + line)
      line
    }

    def ack(cmd: Cmd): Ack = {
      write(cmd)
      Parser.ack(read())
    }

    def info(attr: String): Info = {
      write(GetInfo(attr))
      Info(read())
    }

    def check(): IsSat = {
      write(CheckSat)
      Parser.issat(read())
    }

    def labels(): Labels = {
      write(Labels)
      Parser.labels(read())
    }

    def model(state: State): Model = {
      write(GetModel)
      val parser = new Parser(state)
      Model(parser.model(read()))
    }
  }
  implicit class ProcessWithPid(process: java.lang.Process) { def pid = 0 }
}

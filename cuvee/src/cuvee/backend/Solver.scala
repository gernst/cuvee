package cuvee.backend

import cuvee.pure._
import cuvee.smtlib._
import java.io.BufferedReader
import java.io.PrintStream

trait Sink {
  // unsafe on commands that don't ack
  def ack(cmd: Cmd): Ack

  def check(): IsSat
  def model(): Model
  def assertions(): Assertions

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
      case GetAssertions =>
        assertions()
    }

  def control(cmd: Ctrl) =
    ack(cmd)

  def declare(cmd: Decl) =
    ack(cmd)

  def assert(expr: Expr) =
    ack(Assert(expr))

  def assert(exprs: List[Expr]): Any = {
    exprs.foldLeft(())((_, expr) => assert(expr))
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
}

object Sink {
  class tee(primary: Solver, secondary: Sink*) extends Solver {
    def ack(cmd: Cmd) = {
      for (that <- secondary)
        that ack cmd
      primary ack cmd
    }

    def check() = {
      for (that <- secondary)
        that.check()
      primary.check()
    }

    def model() = {
      for (that <- secondary)
        that.model()
      primary.model()
    }

    def assertions() = {
      for (that <- secondary)
        that.assertions()
      primary.assertions()
    }
  }
}

trait Solver extends Sink {
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
}

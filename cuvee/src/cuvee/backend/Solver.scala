package cuvee.backend

import cuvee.pure._
import cuvee.smtlib._
import java.io.BufferedReader
import java.io.PrintStream

trait Solver {
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
  object dummy extends Solver {
    def ack(cmd: Cmd) = Success
    def check() = Unknown
    def model() = cuvee.error("no model")
  }
}

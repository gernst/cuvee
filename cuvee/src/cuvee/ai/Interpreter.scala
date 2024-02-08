package cuvee.ai

import cuvee.pure._
import cuvee.imp._

trait Interpreter[S] {

  def assign(xs: List[Var], rhs: List[Expr], states: List[S]): List[S]

  def positive(expr: Expr, states: List[S]): List[S]
  def negative(expr: Expr, states: List[S]): List[S]

  def widen(init: List[S], states: List[S]): List[S]
  def narrow(init: List[S],states: List[S]): List[S]

  def isSubsetOf(states1: List[S], states2: List[S]): Boolean

  def fixpoint(init: List[S], fuel: Int = 5)(next: List[S] => List[S]): List[S] = {
    assert(fuel >= 0)

    val states = next(init)

    if (isSubsetOf(states, init))
      states
    else
      fixpoint(states, fuel - 1)(next)
  }

  def invariants(states: List[S]): Expr

  def local(xs: List[Var], rhs: List[Expr], states: List[S]): List[S]

  def execBlock(progs: List[Prog], states: List[S]): List[S] = progs match {
    case (x: Prog) :: (rest: List[Prog]) =>
      val st_ = exec(x, states)
      execBlock(rest, st_)

    case Nil =>
      states
  }

  def exec(prog: Prog, states: List[S]): List[S] = prog match {
    case Assign(xs, rhs) =>
      assign(xs, rhs, states)

    case If(test, left, right) =>
      val states1 = exec(left, positive(test, states))
      val states2 = exec(right, negative(test, states))
      states1 ++ states2

    case While(test, body, term, inv, sum, frames) =>
      val widened = fixpoint(states) { states =>
        val states_ = exec(body, positive(test, states))
        val result = widen(states, states_)
        result
      }

      val narrowed = fixpoint(widened) { states =>
        val states_ = exec(body, positive(test, states))
        val result = narrow(states, states_)
        result
      }
     
      val inv_ = invariants(narrowed)

      val res = negative(test, narrowed)
      res      
    
    case Block(progs) => 
      execBlock(progs, states)

    case Local(xs, rhs) => 
     local(xs, rhs, states)

    case Spec(Nil, True, psi) => // assume
      val res = positive(psi, states)
      res

    case Spec(Nil, phi, True) => // assert
      val ps = positive(phi, states)
      val ng = negative(phi, states)

      if (ng.isEmpty) ps
      else throw new Exception("Exception occured while executing Assert. Reason: negative Test is not empty is not empty.\nps: " + ps +"\nng: " + ng)

  }
}
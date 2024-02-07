package cuvee.ai

import cuvee.pure._
import cuvee.imp._
import easyparse.map

class Annotator[S](val interpreter: Interpreter[S]) {
  import interpreter._

  def annotateBlock(progs: List[Prog], states: List[S]): (List[Prog], List[S]) = progs match {
    case (prog: Prog) :: (rest: List[Prog]) =>
      val (prog_, st_) = annotate(prog, states)
      val (rest_, st__) = annotateBlock(rest, st_)
      (prog_ :: rest_, st__)

    case Nil =>
      (Nil, states)
  }

  def annotate(prog: Prog, states: List[S]): (Prog, List[S]) = prog match {
    case Assign(xs, rhs) =>
      (prog, assign(xs, rhs, states))

    case If(test, left, right) =>
      val (left_, states1) = annotate(left, positive(test, states))
      val (right_, states2) = annotate(right, negative(test, states))
      val prog_ = If(test, left_, right_)
      (prog_, states1 ++ states2)

    case While(test, body, term, inv, sum, frames) =>
      assert(states.nonEmpty)

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

      val inv_ = Simplify.simplify(invariants(narrowed), Map(), Set())

      val exit = negative(test, narrowed)

      val prog_ = While(test, body, term, And(inv, inv_), sum, frames)
      (prog_, exit)
       
    case Block(progs) =>
      val (progs_, states_) = annotateBlock(progs, states)
      (Block(progs_), states_)

    case Local(xs, rhs) => 
     (prog, local(xs, rhs, states))

    case Spec(Nil, True, psi) => // assume
      (prog, positive(psi, states))

    case Spec(Nil, phi, True) => // assert
      val ps = positive(phi, states)
      val ng = negative(phi, states)

      if (ng.isEmpty) (prog, ps)
      else throw new Exception("Exception occured while executing Assert. Reason: negative Test is not empty is not empty")
  }
}
package cuvee.prove

import cuvee.pure._
import cuvee.smtlib.DeclareFun
import cuvee.smtlib._
import cuvee.State
import cuvee.lemmas.deaccumulate.Deaccumulate
import cuvee.lemmas.Enumerate

/** This class
  *
  * @param solver
  *   SMT solver to use to check expressions
  */
class PositiveProver(solver: Solver) extends Prover {
  def exec(cmd: Cmd, state: State) {
    solver.exec(cmd, state)
  }

  
  def reduce(that: Expr, state: State): Expr = that match {
    case Clause(Nil, Nil, phi: Expr) =>
      atom(phi, state)

    case Clause(xs, assms, concls) =>
      disj(xs, assms, List(concls), state) 
  }

  def atom(phi: Expr, state: State): Expr = solver scoped {
    solver.assert(!phi)
    val status = solver.check()

    status match {
      // case Sat =>
      //   Atom(phi, Some(solver.model(state)))
      case Unsat =>
        True
      case Unknown | Sat =>
        phi
    }
  }

  def disj(xs: List[Var], assms: List[Expr], concls: List[Expr], state: State): Expr =
    solver.scoped {
      // A Disj contains variables quantified by a forall quantifier (disj.xs).
      // Below, we'll split those variables from their declaration in the quantifier.
      // Decide how to rename the quantified variables
      val re = Expr.fresh(xs)
      val re_ = re map (_.swap)

      val xs_ = xs rename re
      val assms_ = assms map (_ rename re)
      val concls_ = concls map (_ rename re)

      // Declare the variables from the forall-quantifier
      for (x <- xs_)
        solver.ack(DeclareFun(x.name, Nil, Nil, x.typ))

      for (pre <- assms_)
        solver assert pre

      if (concls.isEmpty && solver.isUnsat) {
        // Empty succedent: the only option to close the proof
        // is when the assumptions are already inconsistent.
        // However, do not do this eagerly, because *typically*
        // they are not inconsistent if we have a proper goal.
        True
      } else {
        // Otherwise: Attempt to prove one formula of the succedent,
        // will succeed anyway if the assumptions are already inconsistent
        val concls__ = any(concls_, state)
        // undo the renaming
        Clause(xs, assms_ map (_ rename re_), Or(concls__ map (_ rename re_)))

      }
    }

  def any(concls: List[Expr], state: State): List[Expr] = concls match {
    case Nil =>
      Nil

    case first :: rest =>
      reduce(first, state) match {
        case Exists(_, Or(List(False))) =>
          any(rest, state)
        case first_ =>
          solver.scoped {
            // justification: A \/ B  <==>  (A \/ (!A ==> B))
            solver.assert(!first_)
            first_ :: any(rest, state)
          }
      }
  }

  def all(exprs: List[Expr], state: State): List[Expr] = exprs match {
    case Nil =>
      Nil

    case first :: rest =>
      reduce(first, state) match {
        case first_ @ True =>
          all(rest, state)

        case first_ =>
          solver.scoped {
            // justification: A /\ B  <==>  (A /\ (A ==> B))
            solver.assert(first_)
            first_ :: all(rest, state)
          }
      }
  }
}

object PositiveProver {
  def main(args: Array[String]): Unit = try {
    val occur = 2
    val depth = 4

    val funs = List(
      Fun.not,
      Fun.and,
      Fun.or,
      Fun.imp
    )

    def atom(name: String): Expr =
      App(Fun(name, Nil, Nil, Sort.bool), Nil)

    val names = List("A", "B", "C", "D")

    val builtin = Map(
      True -> occur,
      False -> occur
    )
    
    val atoms = Map(names map (name => (atom(name) -> occur)): _*)

    val phis = Enumerate.enumerate(Sort.bool, funs, atoms ++ builtin, depth)

    val solver = Solver.z3()

    for(name <- names) {
      val cmd = DeclareFun(name, Nil, Nil, Sort.bool)
      solver.ack(cmd)
    }

    for ((phi, _) <- phis) {
      val psi = phi //TODO replace from with simplification?

      val ok = solver.isTrue(phi === psi)

      if (!ok) {
        println(phi)
        println(psi)
        return
      }
    }
  } catch {
    case e: Throwable =>
      println(e)
  }
}

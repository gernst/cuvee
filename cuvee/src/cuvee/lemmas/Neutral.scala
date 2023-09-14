package cuvee.lemmas

import cuvee.State
import cuvee.pure._
import cuvee.smtlib.Solver
import cuvee.prove.InductiveProver

object Neutral {
  def holds(phi: Expr, x: Var, st: State, solver: Solver) = x.typ match {
    case Sort(Con(name, _), _) if st.datatypes contains name =>
      val dt = st datatypes name
      val ind = InductiveProver.induction(phi, x, dt)
      lazy val a = solver.isTrue(phi)
      lazy val b = solver.isTrue(ind)

      (a || b, !a && b)

    case _ =>
      // don't generate lemmas for non-ADT functions
      (solver.isTrue(phi), false)
  }

  def findNeutral(
      f: Fun,
      st: State,
      solver: Solver
  ): (List[Either[(Fun, Expr), (Fun, Expr)]], List[(Rule, String)]) = {
    (f.args, f.res) match {
      case (List(left, right), res @ Sort(Con(name, _), _))
          if left == res && right == res && (st.datatypes contains name) =>
        val dt = st datatypes name

        val base =
          for ((c, Nil) <- dt.constrs)
            yield App(c, res)

        val x = Var("x", left)
        val y = Var("y", right)

        val lefts = for (c <- base) yield {
          val lhs = App(f, List(c, y))
          val rhs = y
          val phi = Forall(List(y), Eq(lhs, rhs))

          val (proved, inductive) = holds(phi, y, st, solver)
          val neutrals = if (proved) List(Left((f, c))) else Nil
          val eqs = if (inductive) List(Rule(lhs, rhs) -> "left neutral") else Nil

          (neutrals, eqs)
        }

        val rights = for (c <- base) yield {
          val lhs = App(f, List(x, c))
          val rhs = x
          val phi = Forall(List(x), Eq(lhs, rhs))

          val (proved, inductive) = holds(phi, x, st, solver)
          val neutrals = if (proved) List(Right((f, c))) else Nil
          val eqs = if (inductive) List(Rule(lhs, rhs) -> "right neutral") else Nil

          (neutrals, eqs)
        }

        val all = lefts ++ rights
        val (neutrals, eqs) = all.unzip
        (neutrals.flatten, eqs.flatten)

      case _ =>
        (Nil, Nil)
    }
  }

  def findNeutral(
      funs: List[Fun],
      st: State,
      solver: Solver
  ): (List[Either[(Fun, Expr), (Fun, Expr)]], List[(Rule, String)]) = {
    val all = funs map { findNeutral(_, st, solver) }
    val (neutrals, eqs) = all.unzip
    (neutrals.flatten, eqs.flatten)
  }
}

package cuvee.backend

import cuvee.State
import cuvee.util.Name
import cuvee.pure._
import cuvee.smtlib._


object InductiveProver {
  def holds(prelude: List[Cmd], goal: Expr) = {
    prove(prelude, goal) == Unsat
  }

  def holdsByInduction(
      prelude: List[Cmd],
      goal: Expr,
      datatypes: Map[Name, Datatype]
  ) = {
    proveWithInduction(prelude, goal, datatypes) exists { case (x, issat) =>
      issat == Unsat
    }
  }

  def prove(prelude: List[Cmd], goal: Expr): IsSat = {
    val solver = Solver.z3()

    for (cmd <- prelude)
      solver.exec(cmd)

    // println("   " + goal)
    val result = solver.check(Not(goal))

    // solver.exec(Exit)
    // solver.destroy()
    result
  }

  def proveWithInduction(
      prelude: List[Cmd],
      goal: Expr,
      datatypes: Map[Name, Datatype]
  ): LazyList[(Var, IsSat)] = {
    val solver = Solver.z3()

    try {
      for (cmd <- prelude) {
        solver.exec(cmd)
      }

      proveWithInduction(solver, goal, datatypes)
    } finally {
    //   solver.exec(Exit)
    //   solver.destroy()
    }
  }

  def proveWithInduction(
      solver: Solver,
      goal: Expr,
      datatypes: Map[Name, Datatype]
  ): LazyList[(Var, IsSat)] = {
    val candidates = LazyList(inductions(goal, datatypes): _*)

    for ((x, goal_) <- candidates)
      yield {
        // println("   " + goal_)
        (x, solver.check(Not(goal_)))
      }
  }

  def inductionVariables(
      phi: Expr,
      datatypes: Map[Name, Datatype]
  ): List[(Var, Datatype)] = {
    val Clause(formals, ant, suc) = phi

    for (xt @ Var(x, Sort(con, args)) <- formals if datatypes contains con.name)
      yield (xt, datatypes(con.name))
  }

  def inductions(
      phi: Expr,
      datatypes: Map[Name, Datatype]
  ): List[(Var, Expr)] = {
    for ((x, dt) <- inductionVariables(phi, datatypes))
      yield x -> induction(phi, x, dt)
  }

  def induction(
      sort: Sort,
      dt: Datatype
  ): List[(Inst, List[Var], List[Int])] = {
    val Sort(con, args) = sort
    val Datatype(params, constrs) = dt
    val su = Type.subst(params, args)

    for ((constr, sels) <- constrs) yield {
      // fresh variables for each constructor argument, named as the selectors
      val args =
        for (Fun(name, _, _, res) <- sels)
          yield Expr.fresh(name, res subst su)

      val hyps =
        for ((Var(_, Sort(con_, _)), i) <- args.zipWithIndex if con_ == con)
          yield i

      (Inst(constr, su), args, hyps)
    }
  }

  def induction(phi: Expr, x: Var, dt: Datatype): Expr = {
    val Var(name, t: Sort) = x
    val Clause(xs, ant, suc) = phi

    val ind = induction(t, dt)

    val phis = for ((constr, args, hyps) <- ind) yield {
      val expr = App(constr, args)

      val prems = for (i <- hyps) yield {
        val y = args(i)
        val re = Map(x -> y)

        Clause(
          Nil, // xs filter (_ != x),
          ant rename re,
          suc rename re
        )
      }

      val su = Map(x -> expr)
      Clause(args, prems ++ (ant subst su), suc subst su)
    }

    Forall(xs, And(phis))
  }
}

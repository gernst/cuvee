package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.backend.InductiveProver
import cuvee.smtlib._
import cuvee.util.Main
import cuvee.util.Run
import cuvee.backend.Solver

object enat extends Run(Enumerate, "examples/boogie/nat.bpl")

object Enumerate extends Main {
  import InductiveProver._

// cuvee.smtlib.solver.debug = true

  def findEqual(
      solver: Solver,
      funs: LazyList[Fun],
      consts: LazyList[Expr],
      lhs: Expr,
      repeat: Int,
      depth: Int,
      rws: Map[Fun, List[Rule]],
      st: State
  ) {

    val free = lhs.free.toList
    val vars = Map(free map (_ -> repeat): _*)
    val candidates = Deaccumulate.enumerate(funs, consts, lhs.typ, vars, depth)

    var results: Set[Expr] = Set()

    for ((rhs, _) <- candidates if lhs != rhs) {
      val goal = Forall(free.toList, Eq(lhs, rhs))
      // print("candidate: " + goal)

      // val proved = solver.check(Not(goal)) match {
      //   case Unknown =>
      //     proveWithInduction(solver, goal, st.datatypes) exists { case (x, status) =>
      //       status == Unsat
      //     }
      //   case Unsat => true
      //   case _     => false
      // }

      val proved = inductions(goal, st.datatypes) exists { case (x, goal) =>
        Simplify.simplify(goal, rws, st.constrs) match {
          case True =>
            true
          case res =>
            // if(solver.isTrue(goal))
            //   println("missed: " + res)
            false
        }
      }

      if (proved) {
        // println(" proved!")
        println("proved: " + goal)
        results += goal
      } else {
        println("discarded: " + goal)
        // println(" discarded.")
      }
    }
  }

  def findEqual(
      solver: Solver,
      funs: LazyList[Fun],
      consts: LazyList[Expr],
      f: Fun,
      g: Fun,
      i: Int,
      repeat: Int,
      depth: Int,
      rws: Map[Fun, List[Rule]],
      st: State
  ) {
    val xs = Expr.vars("x", f.args)
    val ys = Expr.vars("y", g.args)
    val lhs = App(f, xs updated (i, App(g, ys)))

    findEqual(solver, funs, consts, lhs, repeat, depth, rws, st)
  }

  def main(args: Array[String]) {
    val Array(file) = args
    val (decls, defs, cmds, st) = read(file)
    println(file)

    val solver = z3(State.default, timeout = 100)

    for (cmd <- cmds)
      solver.exec(cmd)

    val all = cmds collect {
      case DeclareFun(name, params, args, res) =>
        st.funs(name, args.length)

      case DefineFun(name, params, formals, res, body, rec) =>
        st.funs(name, formals.length)
    }

    val funs = LazyList(all: _*)
    val consts = LazyList()

    val nat = st.sort("nat")

    val add = st.funs("add", 2)
    val mul = st.funs("mul", 2)
    val sub = st.funs("sub", 2)

    val x = Var("x", nat)
    val y = Var("y", nat)
    val z = Var("z", nat)

    val rules = Rewrite.from(cmds, st)
    val rws = rules groupBy (_.fun)

    val repeat = 1
    val depth = 3

    // findEqual(solver, funs, consts, add(x, add(y, z)), 1, 3, rws, st)

    for (
      f <- all;
      g <- all;
      (typ, pos) <- f.args.zipWithIndex if typ == g.res
    ) {
      findEqual(solver, funs, consts, f, g, pos, repeat, depth, rws, st)
    }
  }
}

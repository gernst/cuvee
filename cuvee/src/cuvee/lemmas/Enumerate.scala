package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.prove.InductiveProver
import cuvee.smtlib._
import cuvee.util.Main
import cuvee.util.Run

import cuvee.lemmas.deaccumulate.Deaccumulate
object enat extends Run(Enumerate, "examples/boogie/nat.bpl")
object elength extends Run(Enumerate, "examples/boogie/length.bpl")

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
    val base = Map(free ++ consts map (_ -> repeat): _*)
    val candidates = Deaccumulate.enumerate(lhs.typ, funs, base, depth)

    var results: Set[Expr] = Set()
    println("trying " + lhs)

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
            // if (solver.isTrue(res))
            //   // println("missed: " + res)
            //   true
            // else
              false
        }
      }

      if (proved) {
        // println(" proved!")
        println("proved: " + goal)
        results += goal
      } else {
        // println("discarded: " + goal)
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
    val (cmds, st) = read(file)
    val (decls, eqs, defs) = prepare(cmds, st)
    println(file)

    val solver = Solver.z3(timeout = 50)

    for (cmd <- cmds)
      solver.ack(cmd)

    // TODO: add data type constructors
    val all_ = cmds collect {
      case DeclareFun(name, params, args, res) =>
        List(st.funs(name, args.length) -> true)

      case DefineFun(name, params, formals, res, body, rec) =>
        List(st.funs(name, formals.length) -> true)

      case DeclareDatatypes(_, datatypes) =>
        for (
          dt <- datatypes;
          (constr, _) <- dt.constrs
        )
          yield constr -> false
    }

    val (constfuns, nonconstfuns) = all_.flatten.partition {
      case (fun, _) =>
        fun.arity == 0 && fun.params.isEmpty
    }

    val extra = LazyList(st.funs("+", 2))
    val funs = LazyList(nonconstfuns map (_._1): _*)
    val consts = LazyList(Zero, One) ++ (constfuns map { case (fun, _) => new App(Inst(fun, Map()), Nil) })

    val rules = Rewrite.from(cmds, st)
    val rws = rules groupBy (_.fun)

    val repeat = 1
    val depth = 3

    // findEqual(solver, funs, consts, add(x, add(y, z)), 1, 3, rws, st)

    for (
      (f, true) <- nonconstfuns;
      (g, true) <- nonconstfuns;
      (typ, pos) <- f.args.zipWithIndex if typ == g.res
    ) {
      findEqual(solver, funs ++ extra, consts, f, g, pos, repeat, depth, rws, st)
    }
  }
}

package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.prove.InductiveProver
import cuvee.smtlib._
import cuvee.util.Main
import cuvee.util.Run
import cuvee.pipe.Stage

object Enumerate extends Stage {
  import InductiveProver._

  def select(fun: Fun, typ: Type) = {
    try {
      val inst = fun.generic
      val ty = Type.bind(inst.res, typ)
      List((inst subst ty))
    } catch {
      case e: Type.CannotBind =>
        List()
    }
  }

  def enumerate(
      types: List[Type],
      funs: List[Fun],
      base0: Map[Expr, Int],
      depth: Int
  ): List[(List[Expr], Map[Expr, Int])] = types match {
    case Nil =>
      List((Nil, base0))

    case typ :: rest =>
      for (
        (expr, base1) <- enumerate(typ, funs, base0, depth);
        (exprs, base2) <- enumerate(rest, funs, base1, depth)
      )
        yield (expr :: exprs, base2)
  }

  def enumerate(
      typ: Type,
      funs: List[Fun],
      base: Map[Expr, Int],
      depth: Int
  ): List[(Expr, Map[Expr, Int])] = if (depth == 0) {
    List()
  } else {
    val first =
      List.from(
        for ((z, k) <- base if z.typ == typ && k > 0)
          yield (z, base + (z -> (k - 1)))
      )

    val next =
      for (
        fun <- funs;
        inst <- select(fun, typ)
      )
        yield inst

    val second =
      for (
        inst <- next;
        (args, base_) <- enumerate(inst.args, funs, base, depth - 1)
      )
        yield (App(inst, args), base_)

    first ++ second
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) =
    if (cmds.nonEmpty && (last == CheckSat || last == Exit)) {
      val (decls, eqs, defs) = prepare(cmds, state)
      val solver = Solver.z3(timeout = 20)

      for (cmd <- prefix ++ cmds)
        solver.ack(cmd)

      // TODO: add data type constructors
      val all_ = cmds collect {
        case DeclareFun(name, params, args, res) =>
          List(state.funs(name, args.length) -> true)

        case DefineFun(name, params, formals, res, body, rec) =>
          List(state.funs(name, formals.length) -> true)

        case DeclareDatatypes(_, datatypes) =>
          for (
            dt <- datatypes;
            (constr, _) <- dt.constrs
          )
            yield constr -> false
      }

      val (constfuns, nonconstfuns) = all_.flatten.partition { case (fun, _) =>
        fun.arity == 0 && fun.params.isEmpty
      }

      // add some functions with known neutral elements
      val extra =
        List(state.funs("+", 2), state.funs("not", 1), state.funs("and", 2), state.funs("or", 2))

      val funs = List(nonconstfuns map (_._1): _*)

      val consts: List[Expr] =
        List(Zero, One) ++ (constfuns map { case (fun, _) => new App(Inst(fun, Map()), Nil) })

      val constrs = state.constrs
      val rws = eqs groupBy (_.fun)

      val repeat = 1 // at least 2 needed for e.g. for map:append
      val depth = 3 // at least 3 needed for distributive laws
      val rounds = 2

      // compute a set of candidates for each left-hand side
      var candidates = Set[Expr]()

      for (
        (f, true) <- nonconstfuns;
        (g, true) <- nonconstfuns;
        (typ, pos) <- f.args.zipWithIndex if typ == g.res
      ) {
        val xs = Expr.vars("x", f.args)
        val ys = Expr.vars("y", g.args)
        val lhs = App(f, xs updated (pos, App(g, ys)))

        val free = lhs.free.toList
        val base = Map(free ++ consts map (_ -> repeat): _*)

        val exprs =
          for ((rhs, _) <- enumerate(lhs.typ, funs, base, depth))
            yield {
              val phi = Forall(free, Eq(lhs, rhs))
              val goal = Simplify.simplify(phi, rws, constrs)
              goal
            }

        candidates ++= exprs
      }

      var lemmas: List[Lemma] = Nil

      for (round <- 1 to rounds) {
        val count = candidates.size
        // println("round " + round + " (" + count + " candidates)")

        val todo = candidates
        candidates = Set()

        for (goal <- todo) {
          // print(goal)

          solver.check(!goal) match {
            case Sat   => // println(" sat") // wrong
            case Unsat => // println(" unsat") // trivial

            case Unknown =>
              val goals = inductions(goal, state.datatypes)
              val proved = goals exists { case (x, goal) => solver.isTrue(goal) }
              // if (proved) println(" proved") else println(" unknown")

              if (proved) {
                solver.assert(goal)
                lemmas = Lemma(goal, None, true) :: lemmas
              } else {
                candidates += goal
              }
          }
        }
      }

      solver.ack(Exit)
      solver.destroy()

      val goals =
        for ((Assert(Not(phi))) <- cmds)
          yield phi

      val (pre, post) = cmds partition {
        case Assert(Not(expr)) => false
        case _                 => true
      }

      // reversing restores the order in which they were discovered
      pre ++ lemmas.reverse ++ post
    } else {
      cmds
    }
}

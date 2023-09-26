package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.prove.InductiveProver
import cuvee.smtlib._
import cuvee.util.Main
import cuvee.util.Run
import cuvee.pipe.Stage

object enat extends Run(Enumerate, "examples/boogie/nat.bpl")
object elength extends Run(Enumerate, "examples/boogie/length.bpl")

object Enumerate extends Main with Stage {
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

// cuvee.smtlib.solver.debug = true

  def findEqual(
      solver: Solver,
      funs: List[Fun],
      consts: List[Expr],
      lhs: Expr,
      repeat: Int,
      depth: Int,
      rws: Map[Fun, List[Rule]],
      st: State
  ): List[List[Lemma]] = {
    val free = lhs.free.toList
    val base = Map(free ++ consts map (_ -> repeat): _*)

    print("trying " + lhs)
    val candidates = enumerate(lhs.typ, funs, base, depth)
    println(" ...")

    for ((rhs, _) <- candidates if lhs != rhs) yield {
      val goal = Forall(free.toList, Eq(lhs, rhs))
      val goal_ = Simplify.simplify(goal, rws, st.constrs)

      // XXX: simple cex check up to size 2?

      if (goal_ == True) {
        // don't report trivial lemmas
        Nil
      } else {

        // val proved = solver.check(Not(goal)) match {
        //   case Unknown =>
        //     proveWithInduction(solver, goal, st.datatypes) exists { case (x, status) =>
        //       status == Unsat
        //     }
        //   case Unsat => true
        //   case _     => false
        // }

        // println("candidate: " + rhs)
        val proved = inductions(goal_, st.datatypes) exists { case (x, goal) =>
          Simplify.simplify(goal, rws, st.constrs) match {
            case res if solver.isTrue(res) =>
              true
            case _ =>
              false
          }
        }

        if (proved) {
          // println(" proved!")
          println("proved: " + goal)
          List(Lemma(goal, None, false))
        } else {
          Nil
          // println("discarded: " + goal)
          // println(" discarded.")
        }
      }
    }
  }

  def findEqual(
      solver: Solver,
      funs: List[Fun],
      consts: List[Expr],
      f: Fun,
      g: Fun,
      i: Int,
      repeat: Int,
      depth: Int,
      rws: Map[Fun, List[Rule]],
      st: State
  ): List[List[Lemma]] = {
    val xs = Expr.vars("x", f.args)
    val ys = Expr.vars("y", g.args)
    val lhs = App(f, xs updated (i, App(g, ys)))

    findEqual(solver, funs, consts, lhs, repeat, depth, rws, st)
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) =
    if (cmds.nonEmpty && (last == CheckSat || last == Exit)) {
      val (decls, eqs, defs) = prepare(cmds, state)
<<<<<<< HEAD
      val solver = Solver.z3(timeout = 20)
=======
      val solver = Solver.z3(timeout =20)
>>>>>>> f66740ff76d8122aa78332511fe1d11da7afbe4e

      for (cmd <- cmds)
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

      val consts =
        List(Zero, One) ++ (constfuns map { case (fun, _) => new App(Inst(fun, Map()), Nil) })

      val rws = eqs groupBy (_.fun)

      val repeat = 1
      val depth = 3

      val add =
        for (
          (f, true) <- nonconstfuns;
          (g, true) <- nonconstfuns;
          (typ, pos) <- f.args.zipWithIndex if typ == g.res;
          lemmas <- findEqual(solver, funs ++ extra, consts, f, g, pos, repeat, depth, rws, state);
          res <- lemmas
        ) yield {
          res
        }

      val goals =
        for ((Assert(Not(phi))) <- cmds)
          yield phi

      solver.ack(Exit)
      solver.destroy()

      val (pre, post) = cmds partition {
        case Assert(Not(expr)) => false
        case _                 => true
      }

      pre ++ add ++ post
    } else {
      cmds
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

    val (constfuns, nonconstfuns) = all_.flatten.partition { case (fun, _) =>
      fun.arity == 0 && fun.params.isEmpty
    }

    val extra = List(st.funs("+", 2))
    val funs = List(nonconstfuns map (_._1): _*)
    val consts =
      List(Zero, One) ++ (constfuns map { case (fun, _) => new App(Inst(fun, Map()), Nil) })

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

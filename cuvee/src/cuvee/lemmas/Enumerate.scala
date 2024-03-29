package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.prove.InductiveProver
import cuvee.smtlib._
import cuvee.util.Main
import cuvee.util.Run
import cuvee.pipe.Stage
import cuvee.prove.QuickCheck
import cuvee.util.Fix
import scala.util.Try
import java.time.format.DateTimeFormatter
import java.time.LocalDateTime

object Enumerate {
  var debug = true
  var trace = false

  def depthOf(e: Expr): Int = e match {
    case x: Var      => 1
    case l: Lit      => 1
    case App(_, Nil) => 1
    case App(_, args) =>
      val ds = args map depthOf
      1 + ds.max
    case Bind(quant, formals, body, typ) =>
      depthOf(body) + 1
  }

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

  val builtin = State.default.funs.values.toSet
}

class Enumerate(rounds: Int) extends Stage {
  import Enumerate._

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) =
    if (cmds.nonEmpty && (last == CheckSat || last == Exit)) {
      val (decls, eqs, defs) = prepare(cmds, state)
      var solver = Solver.z3(timeout = 50)

      for (cmd <- prefix ++ cmds)
        solver.ack(cmd)

      val reinit = scala.collection.mutable.Buffer(prefix ++ cmds: _*)

      val constrs = state.constrs
      val rws = eqs groupBy (_.fun)
      val ok = rws.keySet | constrs | builtin

      val (_, _, deps) = Fix.rtc(rws map { case (fun, eqs) => (fun, eqs flatMap (_.funs)) })
      // deps map println
      val all = (constrs ++ rws.keys).toList filter { fun =>
        !(deps contains fun) || (deps(fun) subsetOf ok)
      }

      val (constfuns, nonconstfuns) = all.partition { fun =>
        fun.arity == 0 && fun.params.isEmpty
      }

      // add some functions with known neutral elements
      val extra =
        List(state.funs("+", 2), state.funs("not", 1), state.funs("and", 2), state.funs("or", 2))

      val funs = List(nonconstfuns: _*)

      val consts: List[Expr] =
        List(Zero, One) ++ (constfuns map { fun => new App(Inst(fun, Map()), Nil) })

      val repeat = 2 // at least 2 needed for e.g. for map:append
      val depth = 3 // at least 3 needed for distributive laws
      val rounds = 3

      // compute a set of candidates for each left-hand side
      var candidates = Set[Expr]()

      def list[A](f: => A) = try {
        List(f)
      } catch {
        case _: Exception => Nil
      }

      val init =
        for (
          f <- nonconstfuns if f.params.isEmpty;
          g <- nonconstfuns;
          (typ, pos) <- f.args.zipWithIndex;
          ty <- list(Type.bind(g.res, typ)) // instantiate g, was if typ == g.res
        ) yield {
          val xs = Expr.vars("x", f.args)
          val ys = Expr.vars("y", g.args subst ty)
          val lhs = App(f, xs updated (pos, App(Inst(g, ty), ys)))

          val free = lhs.free.toList
          val params = free.types.free
          require(params.isEmpty, "lhs " + lhs + " has type parameters: " + params)

          (free, lhs)
        }

      val n = init.length
      for (((free, lhs), i) <- init.zipWithIndex) {
        val base = Map(free ++ consts map (_ -> repeat): _*)
        if (debug)
          println(i + " of " + n)

        val exprs =
          for ((rhs, _) <- enumerate(lhs.typ, funs, base, depth))
            yield {
              val phi = Forall(free, Eq(lhs, rhs))
              val goal = Simplify.simplify(phi, rws, constrs)
              goal
            }

        candidates ++= exprs
      }

      val dtf = DateTimeFormatter.ofPattern("HH:mm:ss");

      var lemmas: List[Lemma] = Nil
      val qc = new QuickCheck(rws, state)
      var done = 0

      for (round <- 1 to rounds) {
        val count = candidates.size
        if (debug)
          println("round " + round + " (" + count + " candidates)")

        // try smaller right hand sides first
        val todo = candidates.toList sortBy depthOf
        candidates = Set()
        val n = todo.size

        for ((goal, i) <- todo.zipWithIndex) {
          if (debug) {
            val now = LocalDateTime.now();
            print(dtf.format(now) + " round " + round + " candidate " + i + "/" + n + " " + goal)
          }

          // if ((i + 1) % 10000 == 0) {
          //   if(debug)
          //     println("reinit solver")
          //   solver.ack(Exit)
          //   solver.destroy()

          //   solver = Solver.z3(timeout = 50)
          //   for (cmd <- reinit)
          //     solver.ack(cmd)
          // }

          if (qc.hasSimpleCounterexample(goal, 3)) {
            if (debug) println(" cex")
          } else {
            solver.check(!goal) match {
              case Sat =>
                if (debug) println(" sat") // wrong

              case Unsat =>
                if (debug) println(" unsat") // trivial

              case Unknown =>
                val goals = InductiveProver.inductions(goal, state.datatypes)
                val proved = goals exists { case (x, goal) => solver.isTrue(goal) }

                if (proved) {
                  if (debug) println(" proved")
                  solver.assert(goal)
                  reinit += Assert(goal)
                  lemmas = Lemma(goal, None, true) :: lemmas
                } else {
                  if (debug) println(" unknown")
                  candidates += goal
                }
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

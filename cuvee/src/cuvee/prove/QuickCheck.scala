package cuvee.prove

import cuvee.State
import cuvee.pure._
import cuvee.smtlib._
import cuvee.lemmas.Enumerate
import cuvee.pipe.Stage

//   def enumerate(
//       types: List[Type],
//       funs: List[Fun],
//       base0: Map[Expr, Int],
//       depth: Int

object QuickCheck extends Stage {
  val depth = 3

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) = {
    val all = prefix ++ cmds

    val rws = Rewrite.from(all, state)
    val qc = new QuickCheck(rws.groupBy(_.fun), state)

    cmds map {
      case cmd @ Lemma(expr, tactic, assert) =>
        if (qc.hasSimpleCounterexample(expr, depth))
          cuvee.error("simple counterexample to lemma found: " + expr)
        else
          cmd
      case cmd =>
        cmd
    }
  }
}

class QuickCheck(rws: Map[Fun, List[Rule]], state: State) {
  val constrs = state.constrs

  val anon =
    for ((name, con) <- state.cons.toList if !(state.datatypes contains name) && con.arity == 0)
      yield state.sort(name) // assumes anonymous sorts have no params

  def hasSimpleCounterexample(phi: Expr, depth: Int): Boolean = {
    phi match {
      case Forall(xs, body) =>
        val repeat = 1
        val nconsts = 2

        // for anonymous sorts come up with a carrier of nconsts distinct elements

        val consts =
          for (sort <- anon; index <- 0 until nconsts)
            yield Fun(sort.toString + index, Nil, Nil, sort)

        val base = Map(consts map { c => (App(c, c.res): Expr) -> repeat }: _*)
        val candidates = Enumerate.enumerate(xs.types, constrs.toList, base, depth)

        candidates exists { case (es, _) =>
          val su = Expr.subst(xs, es)
          val body_ = body subst su
          val body__ = Simplify.simplify(body_, rws, constrs ++ consts)
          // println(body__)
          body__ == False
        }

      case _ =>
        false
    }
  }
}

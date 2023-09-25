package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.smtlib._
import cuvee.util.Tool
import cuvee.util.Name
import cuvee.prove.InductiveProver
import cuvee.pipe.Stage
import cuvee.lemmas.prepare

import cuvee.lemmas.deaccumulate.Deaccumulate

object Lemmas extends Stage {
  val rounds = 3

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) =
    if (cmds.nonEmpty && (last == CheckSat || last == Exit)) {
      val (decls, eqs, defs) = prepare(cmds, state)
      // val results = cuvee.lemmas.Test.run(decls, cmds, defs, state)

      implicit val solver = Solver.z3(100)
      Deaccumulate.neutral = Deaccumulate.defaultNeutral

      for (cmd <- cmds) cmd match {
        case SetLogic(_)      =>
        case _: Lemma         =>
        case Assert(Not(phi)) =>
        case _ =>
          solver.exec(cmd, null)
      }

      val goals =
        for ((Assert(Not(phi))) <- cmds)
          yield phi

      val lemmas = new Discover(decls, cmds, defs, state, solver)

      for (
        Lemma(phi, _, _) <- cmds;
        Rule(lhs, rhs, cond, Nil) <- Rules.from(phi, lemmas.original)
      ) {
        lemmas.addLemma("provided", lhs, rhs, cond)
      }

      lemmas.findNeutral(defs map (_.fun))

      for (df <- defs) {
        lemmas.define(df)
        lemmas.deaccumulate(df)
        lemmas.recognizeConditional(df)
      }

      for (df <- defs; dg <- defs) {
        lemmas.fuse(df, dg)
      }

      for (i <- 0 until rounds) {
        lemmas.round()
        lemmas.cleanup()
        lemmas.next()
      }

      val results = lemmas.lemmas

      solver.ack(Exit)
      solver.destroy()

      val known = state.funs.values.toSet
      val add =
        for ((origin, rule) <- results if (origin != "provided") && (rule.funs subsetOf known))
          yield Lemma(rule.toExpr, None, true)

      val (pre, post) = cmds partition {
        case Assert(Not(expr)) =>
          false
        case _ =>
          true
      }
      pre ++ add ++ post
    } else {
      cmds
    }
}

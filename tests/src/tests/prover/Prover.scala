package tests.prover

import cuvee.backend.Prove
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Generator
import cuvee.util.Name
import cuvee.State

object Prover {
  def run(atomCnt: Int, depth: Int) {
    var state = State.default
    val solver = z3(state)
    val prover = new Prove(solver)

    val atomNames = for (id <- (1 to atomCnt).toList) yield Name("x", Some(id))
    val atoms =
      for (name <- atomNames)
        yield App(Inst(Fun(name, Nil, Nil, Sort.bool), Map.empty), Nil)

    solver.scoped({
      for (atom <- atomNames)
        solver.declare(DeclareFun(atom, Nil, Sort.bool))

      for (phi <- Generator.propositionalExprs(atoms, depth)) {
        val res = prover.prove(Prop.from(phi))

        val equiv = makeIff(phi, res.toExpr)
        assert(
          solver.isTrue(equiv),
          f"Solver found that ${res} is not equivalent to to prover input ${phi}."
        )
      }
    })
  }

  def makeIff(phi: Expr, psi: Expr): Expr = And(Imp(phi, psi), Imp(psi, phi))
}

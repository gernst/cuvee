package tests.prover

import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Generator
import cuvee.util.Name
import cuvee.State
import cuvee.backend.PositiveProver

object Prover {
  def run(atomCnt: Int, depth: Int) {
    var state = State.default
    val solver = z3(state)
    val prover = new PositiveProver(solver)

    val atomNames = List.tabulate(atomCnt)(i => Name("x", Some(i)))
    val atoms =
      for (name <- atomNames)
        yield App(Inst(Fun(name, Nil, Nil, Sort.bool), Map.empty), Nil)

    solver.scoped({
      for (atom <- atomNames)
        solver.declare(DeclareFun(atom, Nil, Nil, Sort.bool))

      for (phi <- Generator.propositionalExprs(atoms, depth)) {
        val res = prover.prove(Prop.from(phi))

        val equiv = Eq(phi, res.toExpr)
        assert(
          solver.isTrue(equiv),
          f"Solver found that ${res} is not equivalent to to prover input ${phi}."
        )
      }
    })
  }
}

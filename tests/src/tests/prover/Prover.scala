package tests.prover

import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Generator
import cuvee.util.Name
import cuvee.State
import cuvee.prove.PositiveProver

object Prover {
  def run(atomCnt: Int, depth: Int) {
    var state = State.default
    val solver = Solver.z3()
    val prover = new PositiveProver(solver)

    val atomNames = List.tabulate(atomCnt)(i => Name("x", Some(i)))
    val atoms =
      for (name <- atomNames)
        yield App(Inst(Fun(name, Nil, Nil, Sort.bool), Map.empty), Nil)

    solver.scoped({
      for (atom <- atomNames)
        solver.declare(DeclareFun(atom, Nil, Nil, Sort.bool))

      for (phi <- Generator.propositionalExprs(atoms, depth)) {
        val res = prover.reduce(Prop.from(phi))

        val equiv = Eq(phi, res.toExpr)
        assert(
          solver.isTrue(equiv),
          f"Solver found that ${res} is not equivalent to to prover input ${phi}."
        )
      }
    })
  }
}

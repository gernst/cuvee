package cuvee

import cuvee.pure.Expr
import cuvee.smtlib.Solver
import cuvee.prove.QuickCheck

package object util {
  implicit class TheoryComparison(TA: List[Expr]) {
    def nontrivial(implicit solver: Solver) =
      advantageOver(Nil)

    def reducedGreedily(implicit solver: Solver) =
      solver.scoped {
        TA.filter { case phi =>
          if (solver.isTrue(phi)) {
            false
          } else {
            solver.assert(phi)
            true
          }
        }
      }

    def independentOfAnyOther(implicit solver: Solver) =
      TA.length - dependentOfAnyOther

    def dependentOfAnyOther(implicit solver: Solver) =
      0 until TA.length count { case i =>
        val phi = TA(i)
        val TB = TA.removed(i)

        solver.scoped {
          solver.assert(TB)
          solver.isTrue(phi)
        }
      }

    def advantageOver(TB: List[Expr])(implicit solver: Solver) =
      solver.scoped {
        solver.assert(TB)
        TA count (phi => !solver.isTrue(phi))
      }
  }
}

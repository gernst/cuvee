package cuvee

import cuvee.pure.Expr
import cuvee.smtlib.Solver
import cuvee.prove.QuickCheck

package object util {
  implicit class TheoryComparison(TA: List[Expr]) {
    def nontrivial(implicit solver: Solver) =
      solver.scoped {
        TA filterNot { phi =>
          println(phi)
          solver.isTrue(phi)
        }
      }

    def reduced(implicit solver: Solver): List[Expr] = {
      var TB = reducedGreedily
      if (TA != TB) TB.reduced
      else TA
    }

    def reducedGreedily(implicit solver: Solver) =
      solver.scoped {
        TA.filter { case phi =>
          println(phi)
          if (solver.isTrue(phi)) {
            false
          } else {
            solver.assert(phi)
            true
          }
        }
      }

    def validatedBy(TB: List[Expr])(implicit solver: Solver) =
      solver.scoped {
        solver.assert(TB)
        TA filter { phi =>
          println(phi)
          solver.isTrue(phi)
        }
      }

    def countNontrivial(implicit solver: Solver) =
      advantageOver(Nil)

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
        TA count { phi =>
          !solver.isTrue(phi)
        }
      }
  }
}

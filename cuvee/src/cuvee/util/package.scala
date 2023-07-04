package cuvee

import cuvee.pure.Expr
import cuvee.smtlib.Solver

package object util {

  implicit class TheoryComparison(TB: List[Expr]) {
    def %(TA: List[Expr])(implicit solver: Solver) = {
      val TA_ = solver.scoped {
        solver.assert(TB)
        TA filterNot solver.isTrue
      }

      TA_.length.toFloat / TA.length.toFloat
    }
  }
}

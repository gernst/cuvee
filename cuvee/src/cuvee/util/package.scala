package cuvee

import cuvee.pure.Expr
import cuvee.smtlib.Solver

package object util {

  implicit class TheoryComparison(TA: List[Expr]) {
    def advantageOver(TB: List[Expr])(implicit solver: Solver) =
      if (TA.isEmpty) {
        None // 1.0f // avoid division by zero
      } else {
        val TA_ = solver.scoped {
          solver.assert(TB)
          TA filterNot solver.isTrue
        }

        Some(TA_.length.toFloat / TA.length.toFloat)
      }
  }
}

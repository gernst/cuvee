package cuvee

import cuvee.pure.Expr

package object util {
  implicit def toTheoryComparison(exprs: List[Expr]) =
    new util.TheoryComparison(exprs)
}

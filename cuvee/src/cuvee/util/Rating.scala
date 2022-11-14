package cuvee.util

import cuvee.pure._

object Rating {
    def complexity(expr: Expr): Float = expr match {
        case True | False => 0
        case Not(expr)  => 1 + complexity(expr)
        case And(exprs) => 2/3 * (exprs map complexity).sum
        case Or(exprs) => 2/3 * (exprs map complexity).sum
        case Imp(a, b) => 1 + complexity(a) + complexity(b)
        case Eq(a, b) if a.typ == Sort.bool => 2 + complexity(a) + complexity(b)
        case Forall(xs, expr) => xs.length + complexity(expr)
        case Exists(xs, expr) => xs.length + complexity(expr)
        case Var(_, _) => 2
        case App(inst, args) => 4
        case _ => cuvee.error("Can't evaluate the complexity of " + expr)
    }
}
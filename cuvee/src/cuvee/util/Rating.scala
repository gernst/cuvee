package cuvee.util

import cuvee.pure._

object Rating {
    /** Complexity heuristic for propositions
      *
      * This heuristic provides an estimate of how hard it is to prove a given proposition.
      *
      * @param prop
      * @return
      */
    def complexity(prop: Prop): Int = prop match {
        // Atoms / their expressions are handled in a separate function.
        case Atom(expr, _) =>
            complexity(expr)
        // Conjs and Disj can be defined more easily
        case Conj(xs, neg) =>
            2 + 4 * xs.length + 3 * (neg map complexity).sum
        case Disj(xs, neg, pos) =>
            4 + 4 * xs.length - 3 * (neg map complexity).sum + 3 * (pos map complexity).sum
    }

    /** Complexity heuristic for atomic propositions
      *
      * The heuristic estimates how hard it is to prove a proposition.
      * This function applies only to such expressions which my be contained in an `Atom`,
      * after an expression has been rearranged by a Prop constructor.
      * In particular, we don't handle
      *
      * @param expr
      * @return
      */
    def complexity(expr: Expr): Int = expr match {
        // The `True` / `False` atoms are trivial / not complex
        case True | False => 0
        case Not(expr)  => 1 + complexity(expr)
        // As of now, we're missing complexity values for constants / functions
        case Eq(lhs, rhs) => 2 + complexity(lhs) + complexity(rhs)
        case expr =>
            println(f">>>> Missing complexity estimate for: $expr")
            1
    }
}
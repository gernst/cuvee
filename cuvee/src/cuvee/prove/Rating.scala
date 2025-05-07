package cuvee.prove

import cuvee.pure._
import cuvee.State

object Rating {
    /** Complexity heuristic for atomic propositions
      *
      * The heuristic estimates how hard it is to prove a proposition.
      * This function applies only to such expressions which my be contained in an `Atom`,
      * after an expression has been rearranged by a Prop constructor.
      * In particular, we don't handle operations of propositional logic here,
      * such as conjunctions, disjunctions, implications or negations.
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
            1
    }

    /** Complexity heuristic for atomic propositions
      *
      * The heuristic estimates how hard it is to prove a proposition.
      * This function applies only to such expressions which my be contained in an `Atom`,
      * after an expression has been rearranged by a Prop constructor. 
      * In particular, we don't handle operations of propositional logic here,
      * such as conjunctions, disjunctions, implications or negations.
      *
      * @param expr
      * @return
      */
    def size(expr: Expr)(implicit state: State): Int = expr match {
        // The `True` / `False` atoms are trivial / not complex
        case True | False => 0
        case Not(expr)  => 1 + size(expr)
        // The complexity of a predicate is the complexity of its (expanded body)
        case app @ App(inst, args) if inst.fun.res == Sort.bool && state.fundefs.contains((inst.fun.name, args.length)) =>
            // Generate the function's body with the argumetns substituted for the parameters
            val (params, body) = state.fundefs((inst.fun.name, args.length))
            val su = params.zip(args).toMap
            val expr_ = body.subst(su) //TODO replace removed "Prop.from" + does size work with Expr?
            // Return the body's size
            size(expr_)
        // For all other expressions, return 1.
        case _ => 1
    }
}
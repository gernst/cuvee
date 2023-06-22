package cuvee.prove

import cuvee.pure._
import cuvee.State

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

    /** Size function for propositions.
      *
      * The size calculation is aligned to the size function from our Isabelle proofs
      *
      * However, here we potentially have n-ary conjunctions / disjunctions and also quantified variables!
      *
      * Due to the simplification of cons and disjs, we won't have nested props of the same type.
      *
      * @param prop
      * @return
      */
    def size(prop: Prop)(implicit state: State): Int = prop match {
        // Atoms / their expressions are handled in a separate function.
        case Atom(expr, _) =>
            size(expr)
        // Conjunction: 1 + #vars + sum of arguments' sizes
        case Conj(xs, neg) =>
            1 + xs.length + (neg map size).sum
        // Conjunction: 3 (conjunction, implication, disjunction) + #vars + sum of pos/neg arguments' sizes
        case Disj(xs, neg, pos) =>
            3 + xs.length + (neg map size).sum + (pos map size).sum
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
            val prop = Prop.from(body.subst(su))
            // Return the body's size
            size(prop)
        // For all other expressions, return 1.
        case _ => 1
    }
}
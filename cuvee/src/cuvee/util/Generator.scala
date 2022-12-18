package cuvee.util

import cuvee.pure._

object Generator {
  /** This function generates
    */
  def propositionalExprs(atoms: List[Expr], depth: Int, exactDepth: Boolean = false): Iterable[Expr] = depth match {
    case _ if depth <= 0 => atoms
    case i =>
        var out: List[Expr] = List()

        // If we want to produce propositional formulas of depth *up to* depth, 
        if (!exactDepth)
            out ++= atoms

        for (
            a <- Generator.propositionalExprs(atoms, depth - 1, exactDepth)
        ) {
            // Unary operators
            out :+= Not(a)

            // Binary operators
            for (b <- Generator.propositionalExprs(atoms, depth - 1, exactDepth)) {
                out :+= And(a, b)
                out :+= Or(a, b)
                out :+= Imp(a, b)
            }
        }

        out
  }
}

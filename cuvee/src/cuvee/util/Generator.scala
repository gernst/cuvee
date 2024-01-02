package cuvee.util

import cuvee.pure._

object Generator {
  val ops: List[(Expr, Expr) => Expr] = List(
    (a: Expr, b: Expr) => And(a, b),
    (a: Expr, b: Expr) => Or(a, b),
    Imp,
    ((arg: Expr, _: Expr) => Not(arg))
  )

  /** This function generates
    */
  def propositionalExprs(
      atoms: List[Expr],
      depth: Int,
      exactDepth: Boolean = false
  ): Iterable[Expr] = depth match {
    case _ if depth <= 0 => atoms.view
    case i =>
      val extra = exactDepth match {
        case true  => atoms
        case false => Nil
      }

      for (
        a <- extra.view ++ propositionalExprs(atoms, depth - 1, exactDepth);
        b <- extra.view ++ propositionalExprs(atoms, depth - 1, exactDepth);
        op <- ops.view
      ) yield op(a, b)
  }
  
}

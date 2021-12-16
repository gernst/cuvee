package cuvee.lemmas

import cuvee.pure._

object Util {
  def liftIte(
      fun: Fun,
      inst: Inst,
      rdone: List[Expr],
      todo: List[Expr]
  ): Expr = {
    todo match {
      case Nil =>
        App(fun, inst, rdone.reverse)
      case Ite(test, left, right) :: rest =>
        val _left = liftIte(fun, inst, rdone, left :: rest)
        val _right = liftIte(fun, inst, rdone, right :: rest)
        Ite(test, _left, _right)
      case arg :: rest =>
        liftIte(fun, inst, arg :: rdone, rest)
    }
  }

  def liftIte(expr: Expr): Expr = {
    expr match {
      case App(fun, inst, args) =>
        liftIte(fun, inst, Nil, args)
      case _ =>
        expr
    }
  }
}

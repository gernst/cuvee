package cuvee.lemmas.deaccumulate

import cuvee.pure._
import cuvee.smtlib._

// returned by deaccumulate: (Def, Expr, Fun, List[Fun], List[Rule], List[Cond])

case class Query(b: Fun, oplus: Fun, rest: List[Fun], base: Expr, conds: List[Expr]) {
  def typ = b.res
  def constraints = base :: conds
  def funs = b :: oplus :: rest

  override def toString = {
    funs.mkString("exists\n  ", "\n  ", "\n") + constraints.mkString(
      "where\n  ",
      "\n  ",
      ""
    )
  }

  def cmds = {
    val decls =
      for (Fun(name, params, args, res) <- funs)
        yield DeclareFun(name, params, args, res)

    val conds =
      for (phi <- constraints)
        yield Assert(phi)

    decls ++ conds
  }

}

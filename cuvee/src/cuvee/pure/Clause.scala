package cuvee.pure

object Clause {
//   def apply(formals: List[C], ant: List[Expr], suc: Expr) = {
//     bind(Forall, formals, Imp(And(ant), suc))
//   }

//   def clause(formals: List[Var], ant: List[Expr], suc: List[Expr]) = {
//     Clause(formals, ant, Or(suc))
//   }

  def unapply(expr: Expr) =
    expr match {
      case Forall(xs, Imp(And(ant), suc)) => Some((xs, ant, suc))
      case Forall(xs, suc)                => Some((xs, Nil, suc))
      case Imp(And(ant), suc)             => Some((Nil, ant, suc))
      case _                              => Some((Nil, Nil, expr))
    }
}

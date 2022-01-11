package cuvee.pure

object Clause {
//   def apply(formals: List[C], ant: List[Expr], suc: Expr) = {
//     bind(Forall, formals, Imp(And(ant), suc))
//   }

//   def clause(formals: List[Var], ant: List[Expr], suc: List[Expr]) = {
//     Clause(formals, ant, Or(suc))
//   }

  def apply(xs: List[Var], ant: List[Expr], suc: Expr) =
    (xs, ant) match {
      case (Nil, Nil) => suc
      case (Nil, _)   => Imp(And(ant), suc)
      case (_, Nil)   => Forall(xs, suc)
      case _          => Forall(xs, Imp(And(ant), suc))
    }

  def unapply(expr: Expr) =
    expr match {
      case Forall(xs, Imp(And(ant), suc)) => Some((xs, ant, suc))
      case Forall(xs, suc)                => Some((xs, Nil, suc))
      case Imp(And(ant), suc)             => Some((Nil, ant, suc))
      case _                              => Some((Nil, Nil, expr))
    }
}

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

  def apply(xs: List[Var], ant: Expr, suc: Expr) =
    (xs, ant) match {
      case (Nil, True) => suc
      case (Nil, _)    => Imp(ant, suc)
      case (_, True)   => Forall(xs, suc)
      case _           => Forall(xs, Imp(ant, suc))
    }

  def unapply(expr: Expr) =
    expr match {
      case Forall(xs, Imp(And(ant), suc)) => Some((xs, ant, suc))
      case Forall(xs, Imp(ant, suc))      => Some((xs, List(ant), suc))
      case Forall(xs, suc)                => Some((xs, Nil, suc))
      case Imp(And(ant), suc)             => Some((Nil, ant, suc))
      case Imp(ant, suc)                  => Some((Nil, List(ant), suc))
      case _                              => Some((Nil, Nil, expr))
    }

  def nnf(phi: Expr): Expr = phi match {
    case Not(App(Fun.and, List(phi, psi))) =>
      Or(Simplify.not(nnf(phi)), Simplify.not(nnf(psi)))

    case Not(App(Fun.or, List(phi, psi))) =>
      And(Simplify.not(nnf(phi)), Simplify.not(nnf(psi)))

    case Not(Not(phi)) =>
      nnf(phi)

    case _ =>
      phi
  }

  def dnf(phi: Expr): List[List[Expr]] = phi match {
    case App(Fun.or, List(phi, psi)) =>
      dnf(phi) ++ dnf(psi)

    case App(Fun.and, List(phi, psi)) =>
      for (a <- dnf(phi); b <- dnf(psi))
        yield a ++ b

    case _ =>
      List(List(phi))
  }
}

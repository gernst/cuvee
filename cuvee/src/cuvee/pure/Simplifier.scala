package cuvee.pure

object Simplifier {
  def simplify(expr: Expr): Expr = expr match {
    case And(phis)         => simplifyAnd(phis)
    case Or(phis)          => simplifyOr(phis)
    case Imp(phi, psi)     => simplifyImp(phi, psi)
    case Not(phi)          => simplifyNot(phi)
    case Forall(vars, phi) => simplifyForall(vars, phi)
    case Exists(vars, phi) => simplifyExists(vars, phi)
    case _                 => expr
  }

  def simplifyAnd(phis: List[Expr]): Expr = {
    val phis_f = And.flatten(phis)
    if (phis_f contains False) False
    And(phis_f.distinct filter (_ != True))
  }

  def simplifyOr(phis: List[Expr]): Expr = {
    val phis_f = Or.flatten(phis)
    if (phis_f contains True) True
    Or(phis_f.distinct filter (_ != False))
  }

  def simplifyImp(phi: Expr, psi: Expr): Expr = {
      var phi_ = simplify(phi)
      var psi_ = simplify(psi)

      (phi_, psi_) match {
          case (True, _)        => psi_
          case (_, True)        => True
          case (False, _)       => True
          case (_, False)       => Not(phi_)
          case (d, e) if d == e => True
          case _                => Imp(phi_, psi_)
      }
  }

  def simplifyNot(phi: Expr): Expr = {
    var phi_ = simplify(phi)
    phi_ match {
      case False        => True
      case True         => False
      case Not(psi)     => psi
      case _            => Not(phi_)
    }
  }

  def simplifyForall(vars: List[Var], psi: Expr): Expr = {
    var psi_ = simplify(psi)

    if (vars.isEmpty)
      return psi_

    Forall(vars, psi_)
  }

  def simplifyExists(vars: List[Var], psi: Expr): Expr = {
    var psi_ = simplify(psi)

    if (vars.isEmpty)
      return psi_

    Exists(vars, psi_)
  }
}

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
    var phis_ = phis.map(simplify)
                    .filter(expr => expr != True)
    if (phis_.contains(False))
        return False
    And(phis_)
  }

  def simplifyOr(phis: List[Expr]): Expr = {
    var phis_ = phis.map(simplify)
                    .filter(expr => expr != False)
    if (phis_.contains(True))
        return True
    Or(phis_)
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
      case False => True
      case True  => False
      case _     => Not(phi_)
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

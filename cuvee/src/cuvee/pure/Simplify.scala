package cuvee.pure

object Simplify {
  def simplify(expr: Expr): Expr = expr match {
    case And(phis)         => and(phis)
    case Or(phis)          => or(phis)
    case Imp(phi, psi)     => imp(phi, psi)
    case Not(phi)          => not(phi)
    case Forall(vars, phi) => forall(vars, phi)
    case Exists(vars, phi) => exists(vars, phi)
    case Eq(left, right)   => eq(left, right)
    case _                 => expr
  }

  def eq(left: Expr, right: Expr) = {
    (left, right) match {
      case _ if left == right =>
        True

      case _ =>
        Eq(left, right)
    }
  }

  def and(phis: List[Expr]): Expr = {
    val phis_ = phis map simplify
    val phis_f = And.flatten(phis_)
    if (phis_f contains False) False
    And(phis_f.distinct filter (_ != True))
  }

  def or(phis: List[Expr]): Expr = {
    val phis_ = phis map simplify
    val phis_f = Or.flatten(phis_)
    if (phis_f contains True) True
    Or(phis_f.distinct filter (_ != False))
  }

  def imp(phi: Expr, psi: Expr): Expr = {
    var phi_ = simplify(phi)
    var psi_ = simplify(psi)

    (phi_, psi_) match {
      case (_, True)        => True
      case (False, _)       => True
      case (True, _)        => psi_
      case (_, False)       => Not(phi_)
      case (d, e) if d == e => True
      case _                => Imp(phi_, psi_)
    }
  }

  def not(phi: Expr): Expr = {
    var phi_ = simplify(phi)
    phi_ match {
      case False    => True
      case True     => False
      case Not(psi) => psi
      case _        => Not(phi_)
    }
  }

  def forall(vars: List[Var], psi: Expr): Expr = {
    var psi_ = simplify(psi)
    var vars_ = psi_.free & Set.from(vars)

    if (vars_.isEmpty)
      return psi_

    // Maintain current variable order, but remove variables that are not free in psi_
    Forall(vars filter (vars_ contains _), psi_)
  }

  def exists(vars: List[Var], psi: Expr): Expr = {
    var psi_ = simplify(psi)
    var vars_ = psi_.free & Set.from(vars)

    if (vars_.isEmpty)
      return psi_

    // Maintain current variable order, but remove variables that are not free in psi_
    Exists(vars filter (vars_ contains _), psi_)
  }

  def simplify(prop: Prop): Prop = prop match {
    case Atom(expr)         => atom(expr)
    case Disj(xs, neg, pos) => disj(xs, neg, pos)
    case Conj(xs, neg)      => conj(xs, neg)
  }

  def atom(expr: Expr): Prop = {
    Atom(simplify(expr))
  }

  def disj(xs: List[Var], neg: List[Neg], pos: List[Pos]): Prop = {
    val neg_ = (neg map simplify) filter (_ != Atom(True))
    val pos_ = (pos map simplify) filter (_ != Atom(False))

    if (neg_ contains Atom(False))
      return Atom(True)
    if (pos_ contains Atom(True))
      return Atom(True)

    val neg__ = neg_ map (_.asInstanceOf[Neg])
    val pos__ = pos_ map (_.asInstanceOf[Pos])

    Disj(xs, neg__, pos__)
  }

  def conj(xs: List[Var], neg: List[Neg]): Prop = {
    val neg_ = (neg map simplify) filter (_ != Atom(True))

    if (neg_ contains Atom(False))
      return Atom(False)

    val neg__ = neg_ map (_.asInstanceOf[Neg])

    Conj(xs, neg__)
  }
}

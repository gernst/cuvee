package cuvee.pure

object Simplify {
  def simplify(expr: Expr, rules: Map[Fun, List[Rule]]): Expr = expr match {
    case And(phis)         => and(simplify(phis, rules))
    case Or(phis)          => or(simplify(phis, rules))
    case Not(phi)          => not(simplify(phi, rules))
    case Imp(phi, psi)     => imp(simplify(phi, rules), simplify(psi, rules))
    case Forall(vars, phi) => forall(vars, simplify(phi, rules))
    case Exists(vars, phi) => exists(vars, simplify(phi, rules))
    case Eq(left, right) if left.typ == Sort.bool => eqv(simplify(left, rules), simplify(right, rules))
    case Eq(left, right)   => eq(simplify(left, rules), simplify(right, rules))
    case Bind(quant, formals, body, typ) => bind(quant, formals, simplify(body, rules), typ)

    case App(inst, args) if rules.nonEmpty =>
      // println(" try rewriting: " + expr + " with rules: " + rules)
      val args_ = Rewrite.rewrites(args, rules)
      val expr_ = App(inst, args_)
      // println(" args: " + args_)
      Rewrite.app(expr_, inst.fun, args_, rules, depth = 0)
    // Rewrite.rewrite(expr, rules)

    case _ =>
      expr
  }

  // TODO: maybe simplify should be part of Prop and expr, because this sucks:
  def simplify(prop: Prop, rules: Map[Fun, List[Rule]]): Prop = prop match {
    case Atom(expr, _) => atom(simplify(expr, rules))
    case Disj(xs, neg, pos) =>
      disj(xs, neg map (simplify(_, rules)), pos map (simplify(_, rules)))
    case Conj(xs, neg) => conj(xs, neg map (simplify(_, rules)))
  }

  def simplify(prop: Pos, rules: Map[Fun, List[Rule]]): Pos = prop match {
    case Atom(expr, _)    => atom(simplify(expr, rules))
    case Conj(xs, neg) => conj(xs, neg map (simplify(_, rules)))
  }

  def simplify(prop: Neg, rules: Map[Fun, List[Rule]]): Neg = prop match {
    case Atom(expr, _) => atom(simplify(expr, rules))
    case Disj(xs, neg, pos) =>
      disj(xs, neg map (simplify(_, rules)), pos map (simplify(_, rules)))
  }

  def simplify(exprs: List[Expr], rules: Map[Fun, List[Rule]]): List[Expr] = {
    for (expr <- exprs)
      yield simplify(expr, rules)
  }

  def eq(left: Expr, right: Expr) = {
    (left, right) match {
      case _ if left == right =>
        True

      case _ =>
        Eq(left, right)
    }
  }

  def bind(quant: Quant, formals: List[Var], body: Expr, typ: Type) = {
    val formals_ = formals filter body.free
    if(formals_.isEmpty) body
    else Bind(quant, formals_, body, typ)
  }


  def and(phis: List[Expr]): Expr = {
    val phis_ = And.flatten(phis)
    if (phis_ contains False) False
    And(phis_.distinct filter (_ != True))
  }

  def or(phis: List[Expr]): Expr = {
    val phis_ = Or.flatten(phis)
    if (phis_ contains True) True
    Or(phis_.distinct filter (_ != False))
  }

  def imp(phi: Expr, psi: Expr): Expr = {
    (phi, psi) match {
      case (_, True)       => True
      case (False, _)      => True
      case (True, _)       => psi
      case (_, False)      => not(phi)
      case _ if phi == psi => True
      case _               => Imp(phi, psi)
    }
  }

  def eqv(phi: Expr, psi: Expr): Expr = {
    (phi, psi) match {
      case (_, True)       => phi
      case (False, _)      => not(psi)
      case (True, _)       => psi
      case (_, False)      => not(phi)
      case _ if phi == psi => True
      case _               => Eq(phi, psi)
    }
  }

  def not(phi: Expr): Expr = {
    phi match {
      case False    => True
      case True     => False
      case Not(psi) => psi
      case _        => Not(phi)
    }
  }

  def forall(bound: List[Var], psi: Expr): Expr = {
    Forall(bound, psi) // simplified by quant.apply already
  }

  def exists(bound: List[Var], psi: Expr): Expr = {
    Exists(bound, psi) // simplified by quant.apply already
  }

  def atom(expr: Expr) = {
    Atom(simplify(expr, Map()))
  }

  def disj(xs: List[Var], neg: List[Neg], pos: List[Pos]): Neg = {
    val neg_ = neg map (_.toExpr)
    val pos_ = pos map (_.toExpr)
    Disj.from(xs, neg_, pos_)
  }

  def conj(xs: List[Var], neg: List[Neg]): Pos = {
    val neg_ = neg map (_.toExpr)
    Conj.from(xs, neg_)
  }

  def disj_(xs: List[Var], neg: List[Neg], pos: List[Pos]): Neg = {
    val neg_ = neg filter (_ != Atom(True))
    val pos_ = pos filter (_ != Atom(False))

    if (neg_ contains Atom.f)
      return Atom.t
    if (pos_ contains Atom.t)
      return Atom.t

    // TODO:
    // special case when we collapse to a single pos without bound vars
    // remove irrelevant bound vars

    Disj(xs, neg_, pos_)
  }

  def conj_(xs: List[Var], neg: List[Neg]): Pos = {
    val neg_ = neg filter (_ != Atom(True))

    if (neg_ contains Atom.f)
      return Atom.f

    Conj(xs, neg_)
  }
}

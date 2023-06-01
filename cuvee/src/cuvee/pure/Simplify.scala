package cuvee.pure

import cuvee.smtlib.Model

object Simplify {
  def simplify(rule: Rule, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Rule = {
    val Rule(lhs, rhs, cond, avoid) = rule
    val lhs_ = simplify(lhs, rules, constrs)
    val rhs_ = simplify(rhs, rules, constrs)
    val cond_ = simplify(cond, rules, constrs)
    val avoid_ = avoid map { case (x, e) => (x, simplify(e, rules, constrs)) }
    Rule(lhs_, rhs_, cond_, avoid_)
  }

  def simplify(expr: Expr, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Expr = expr match {
    case And(phis)         => and(simplify(phis, rules, constrs))
    case Or(phis)          => or(simplify(phis, rules, constrs))
    case Not(phi)          => not(simplify(phi, rules, constrs))
    case Imp(phi, psi)     => imp(simplify(phi, rules, constrs), simplify(psi, rules, constrs))
    case Forall(vars, phi) => forall(vars, simplify(phi, rules, constrs))
    case Exists(vars, phi) => exists(vars, simplify(phi, rules, constrs))

    case Eq(left, right) if left.typ == Sort.bool =>
      eqv(simplify(left, rules, constrs), simplify(right, rules, constrs))

    case Eq(left, right) =>
      eq(simplify(left, rules, constrs), simplify(right, rules, constrs), rules, constrs)

    case Bind(quant, formals, body, typ) =>
      bind(quant, formals, simplify(body, rules, constrs), typ)

    case App(inst, args) if rules.nonEmpty =>
      // println(" try rewriting: " + expr + " with rules: " + rules, constrs)
      val args_ = Rewrite.rewrites(args, rules)
      val expr_ = App(inst, args_)
      // println(" args: " + args_)
      val res_ = Rewrite.app(expr_, inst.fun, args_, rules, depth = 0)
      if (expr != res_)
        simplify(res_, rules, constrs)
      else
        res_
    // Rewrite.rewrite(expr, rules, constrs)

    case _ =>
      expr
  }

  // TODO: maybe simplify should be part of Prop and expr, because this sucks:
  def simplify(prop: Prop, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Prop = prop match {
    case Atom(expr, model) =>
      atom(simplify(expr, rules, constrs), model)
    case Disj(xs, neg, pos) =>
      disj(xs, neg map (simplify(_, rules, constrs)), pos map (simplify(_, rules, constrs)))
    case Conj(xs, neg) =>
      conj(xs, neg map (simplify(_, rules, constrs)))
  }

  def simplify(prop: Pos, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Pos = prop match {
    case Atom(expr, model) => atom(simplify(expr, rules, constrs), model)
    case Conj(xs, neg)     => conj(xs, neg map (simplify(_, rules, constrs)))
  }

  def simplify(prop: Neg, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Neg = prop match {
    case Atom(expr, model) =>
      atom(simplify(expr, rules, constrs), model)
    case Disj(xs, neg, pos) =>
      disj(xs, neg map (simplify(_, rules, constrs)), pos map (simplify(_, rules, constrs)))
  }

  def simplify(exprs: List[Expr], rules: Map[Fun, List[Rule]], constrs: Set[Fun]): List[Expr] = {
    for (expr <- exprs)
      yield simplify(expr, rules, constrs)
  }

  def eq(left: Expr, right: Expr, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Expr = {
    (left, right) match {
      case _ if left == right =>
        True

      case (App(Inst(f, _), la), App(Inst(g, _), ra))
          if (constrs contains f) && (constrs contains g) =>
        if (f == g) {
          // unpack arguments as equations
          val eqs =
            for ((l, r) <- (la zip ra))
              yield eq(l, r, rules, constrs)

          and(simplify(eqs, rules, constrs))
        } else {
          // data types are freely generated, so constructors never overlap
          False
        }

      case _ =>
        Eq(left, right)
    }
  }

  def bind(quant: Quant, formals: List[Var], body: Expr, typ: Type) = {
    val formals_ = formals filter body.free
    if (formals_.isEmpty) body
    else Bind(quant, formals_, body, typ)
  }

  def and(phis: List[Expr]): Expr = {
    val phis_ = And.flatten(phis)
    if (phis_ contains False) False
    else And(phis_.distinct filter (_ != True))
  }

  def or(phis: List[Expr]): Expr = {
    val phis_ = Or.flatten(phis)
    if (phis_ contains True) True
    else Or(phis_.distinct filter (_ != False))
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

  def atom(expr: Expr, model: Option[Model] = None) = {
    Atom(simplify(expr, Map(), Set()), model)
  }

  def disj(xs: List[Var], neg: List[Neg], pos: List[Pos]): Neg = {
    Disj.from(xs, neg, pos)
  }

  def conj(xs: List[Var], neg: List[Neg]): Pos = {
    val neg_ = neg map (_.toExpr)
    Conj.from(xs, neg_)
  }

  def prop_(p: Prop): Prop = p match {
    case Atom(expr, cex)    => atom(expr, cex)
    case Disj(xs, neg, pos) => disj_(xs, neg, pos)
    case Conj(xs, neg)      => conj_(xs, neg)
  }

  def disj_(xs: List[Var], neg: List[Neg], pos: List[Pos]): Neg = {
    val neg_ = neg filter (_ != Atom(True))
    val pos_ = pos filter (_ != Atom(False))

    if (neg_ contains Atom.f)
      return Atom.t
    if (pos_ contains Atom.t)
      return Atom.t

    // TODO: special case when we collapse to a single pos without bound vars
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

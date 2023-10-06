package cuvee.pure

import cuvee.smtlib.Model
import cuvee.pure.True
import cuvee.Intersect

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

    case Is(arg, fun) =>
      is(arg, fun)

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

  def simplify(prop: Prop, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Prop = prop match {
    case Atom(expr, None) =>
      Prop.from(simplify(expr, rules, constrs))

    case Atom(expr, model) =>
      Atom(simplify(expr, rules, constrs), model)

    case Disj(xs_, assms_, concls_) =>
      // TODO:
      // - substitute equations
      // - omit unused variables
      // - pull common antecedents out (A ==> B) /\ (A ==> C) ~~> A ==> (B /\ C)
      // - shift negations around?

      var xs = xs_
      var assms = assms_
      var concls = concls_

      var eqs = assms collect {
        case Atom(Eq(x: Var, e), _) if !(x in e) => (x, e)
        case Atom(Eq(e, x: Var), _) if !(x in e) => (x, e)
      }

      val su = Expr.subst(eqs)
      assms = assms map (_ subst su)
      concls = concls map (_ subst su)

      var defs = assms collect {
        case Atom(Eq(x @ App(Inst(f, _), Nil), e), _) if !(f in e) => Rule(x, e)
        case Atom(Eq(e, x @ App(Inst(f, _), Nil)), _) if !(f in e) => Rule(x, e)
      }

      val more = defs.groupBy(_.fun)

      assms = assms_ map (simplify(_, rules ++ more, constrs))
      concls = concls_ map (simplify(_, rules ++ more, constrs))

      val all = concls flatMap { case Conj(xs, props) =>
        props map {
          case _: Atom =>
            Set[Prop]()
          case Disj(xs, assms, concls) =>
            Set(assms: _*)
        }
      }

      if (all.nonEmpty) {
        val common = Intersect(all)

        concls = concls map { case Conj(xs, props) =>
          Conj(
            xs,
            props map {
              case atom: Atom =>
                atom
              case Disj(xs, assms, concls) =>
                Disj(xs, assms filterNot common, concls)
            }
          )
        }

        assms = assms ++ common
      }

      xs = xs filter { case x =>
        assms exists (x in _)
      }

      Disj.reduce(xs, assms, concls)
  }

  def simplify(conj: Conj, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Conj = conj match {
    case Conj(xs, props) =>
      Conj.reduce(xs, props map (simplify(_, rules, constrs)))
  }

  def simplify(exprs: List[Expr], rules: Map[Fun, List[Rule]], constrs: Set[Fun]): List[Expr] = {
    for (expr <- exprs)
      yield simplify(expr, rules, constrs)
  }

  def is(arg: Expr, fun: Fun): Expr = if (true) {
    Is(arg, fun)
  } else {
    val ty = Type.bind(fun.res, arg.typ)
    val unbound = arg.typ.free -- ty.keySet
    require(unbound.isEmpty, "unbound type parameters in " + Is(arg, fun))
    val ts = fun.args subst ty
    val xs = Expr.vars("x", ts)
    Exists(xs, Eq(arg, App(fun, xs)))
  }

  def eq(left: Expr, right: Expr, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Expr = {
    (left, right) match {
      case _ if left == right =>
        True

      case (Lit(left, _), Lit(right, _)) =>
        if (left == right) True
        else False

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

      case (App(Inst(f, _), la), r) if (constrs contains f) && (la contains r) =>
        False
      case (l, App(Inst(g, _), ra)) if (constrs contains g) && (ra contains l) =>
        False

      case _ =>
        Eq(left, right)
    }
  }

  def bind(quant: Quant, formals: List[Var], body: Expr, typ: Type) = quant match {
    case Quant.lambda =>
      ???

    case Quant.exists | Quant.forall =>
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
}

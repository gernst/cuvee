package cuvee.pure

import cuvee.smtlib.Model
import cuvee.pure.True
import cuvee.Intersect
import cuvee.ai.AInt.one
import cuvee.State
import cuvee.sexpr

object Simplify {
  def simplify(rule: Rule, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Rule = {
    val Rule(lhs, rhs, cond, avoid) = rule
    val lhs_ = simplify(lhs, rules, constrs)
    val rhs_ = simplify(rhs, rules, constrs)
    val cond_ = simplify(cond, rules, constrs)
    val avoid_ = avoid map { case (x, e) => (x, simplify(e, rules, constrs)) }
    Rule(lhs_, rhs_, cond_, avoid_)
  }

  def simplify(expr: Expr, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Expr =
    // Expr.liftIte(expr) // don't recursive with liftIte -> may lead to endless loops with nested ites
    expr match {
      case x: Var =>
        x

      case l: Lit =>
        l

      case And(phis) =>
        and(simplify(phis, rules, constrs))

      case Or(phis) =>
        or(simplify(phis, rules, constrs))

      case Not(phi) =>
        not(simplify(phi, rules, constrs))

      case Imp(phi, psi) =>
        imp(simplify(phi, rules, constrs), simplify(psi, rules, constrs))

      case expr @ Ite(test, left, right) =>
        ite(
          simplify(test, rules, constrs),
          simplify(left, rules, constrs),
          simplify(right, rules, constrs)
        )

      case Is(arg, fun) =>
        is(simplify(arg, rules, constrs), fun)

      case At(where, arg) =>
        at(where, simplify(arg, rules, constrs))

      case Eq(left, right) if left.typ == Sort.bool =>
        eqv(simplify(left, rules, constrs), simplify(right, rules, constrs))

      case Eq(left, right) =>
        eq(simplify(left, rules, constrs), simplify(right, rules, constrs), rules, constrs)

      case Bind(quant, formals, body, typ) =>
        bind(quant, formals, simplify(body, rules, constrs), typ)

      case Select(base, index) =>
        select(simplify(base, rules, constrs), simplify(index, rules, constrs))

      case Store(base, index, value) =>
        store(
          simplify(base, rules, constrs),
          simplify(index, rules, constrs),
          simplify(value, rules, constrs)
        )

      // case Distinct(exprs) =>
      //   TODO

      case App(inst, args) =>
        app(expr, inst, simplify(args, rules, constrs), rules, constrs)

      case Note(expr, patterns, attr) =>
        note(simplify(expr, rules, constrs), patterns, attr)
    }

  def app(
      expr: Expr,
      inst: Inst,
      args: List[Expr],
      rules: Map[Fun, List[Rule]],
      constrs: Set[Fun]
  ): Expr = {
    // println(" try rewriting: " + expr + " with rules: " + rules, constrs)
    val args_ = Rewrite.rewrites(args, rules)
    val expr_ = App(inst, args_)
    // println(" args: " + args_)
    val res_ = Rewrite.app(expr_, inst.fun, args_, rules, depth = 0)
    if (expr != res_)
      simplify(res_, rules, constrs)
    else
      builtin(res_, rules, constrs)
  }

  def builtin(expr: Expr, rules: Map[Fun, List[Rule]], constrs: Set[Fun]): Expr = expr match {
    case _ if expr.typ == Sort.int =>
      val poly = Poly(expr)
      val expr_ = poly.compact.toExpr
      // println("expr = " + expr)
      // println("poly = " + poly)
      // println("expr_ = " + expr_)

      if (expr != expr_)
        simplify(expr_, rules, constrs)
      else
        expr_

    case App(inst, args) =>
      App(inst, args map (builtin(_, rules, constrs)))

    case _ =>
      expr
  }

  /*
  def onePoint(assms: List[Expr], su: Map[Var, Expr]): (List[Expr], Map[Var, Expr]) = {
    assms match {
      case Nil =>
        (assms, su)

      case Atom(Eq(x: Var, e), _) :: rest if !(x in e) =>
        val su_ = su + (x -> e)
        val rest_ = rest map (_ subst su_)
        onePoint(rest_, su_)

      case assm :: rest =>
        val (rest_, su_) = onePoint(rest, su)
        (assm :: rest_, su_)
    }
  }
  */

  def simplify(expr: Expr, state: State): Expr = {
    simplify(expr, Map(), state.constrs)
  }

  def simplify(exprs: List[Expr], rules: Map[Fun, List[Rule]], constrs: Set[Fun]): List[Expr] = {
    for (expr <- exprs)
      yield simplify(expr, rules, constrs)
  }

  def note(expr: Expr, patterns: List[List[Expr]], attrs: sexpr.Attrs) =
    expr match {
      case True | False => expr
      case _            => Note(expr, patterns, attrs)
    }

  def at(where: Loc, arg: Expr) = {
    if (arg.free.isEmpty)
      arg
    else
      At(where, arg)
  }

  def is(arg: Expr, fun: Fun): Expr = if (false) {
    Is(arg, fun)
  } else {
    val ty = Type.bind(fun.res, arg.typ)
    val unbound = arg.typ.free -- ty.keySet
    require(unbound.isEmpty, "unbound type parameters in " + Is(arg, fun))
    val ts = fun.args subst ty
    val xs = Expr.vars("x", ts)
    Exists(xs, Eq(arg, App(fun, xs)))
  }

  def select(base: Expr, index: Expr) = {
    base match {
      case Store(_, `index`, value) => value
      case _                        => Select(base, index)
    }
  }

  def store(base: Expr, index: Expr, value: Expr): Expr = {
    (base, value) match {
      case (_, Select(`base`, `index`)) => base
      case (Store(base, `index`, _), _) => store(base, index, value)
      case _                            => Store(base, index, value)
    }
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
      // ???
      // val eqs = onePoint(formals, body, quant == Quant.exists)
      // println(eqs)

      val formals_ = formals filter body.free
      if (formals_.isEmpty) body
      else Bind(quant, formals_, body, typ)
  }

  // def onePoint(bound: List[Var], expr: Expr, ok: Boolean): List[(Var, Expr)] = expr match {
  //   case Eq(x: Var, rhs) if ok && (bound contains x) && !(x in rhs) =>
  //     List(x -> rhs)

  //   case Not(phi) =>
  //     onePoint(bound, expr, !ok)

  //   case And(phis) if ok =>
  //     for (phi <- phis; pair <- onePoint(bound, expr, ok))
  //       yield pair

  //   case Or(phis) if !ok =>
  //     for (phi <- phis; pair <- onePoint(bound, expr, ok))
  //       yield pair

  //   case Imp(phi, psi) =>
  //     onePoint(bound, phi, !ok) ++ onePoint(bound, psi, ok)

  //   case _ =>
  //     Nil
  // }

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

  def ite(test: Expr, left: Expr, right: Expr) = {
    (test, left, right) match {
      case _ if left == right => left
      case (True, _, _)       => left
      case (False, _, _)      => right
      case (_, _, True)       => imp(test, left)
      case (_, True, _)       => imp(not(test), right)
      case (_, _, False)      => and(List(test, left))
      case (_, False, _)      => and(List(not(test), right))
      case _ if test == left  => Or(test, right)
      case _ if test == right => And(test, left)
      case _                  => Ite(test, left, right)
    }
  }

  def forall(bound: List[Var], psi: Expr): Expr = {
    Forall(bound, psi) // simplified by quant.apply already
  }

  def exists(bound: List[Var], psi: Expr): Expr = {
    Exists(bound, psi) // simplified by quant.apply already
  }
}

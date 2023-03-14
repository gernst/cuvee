package cuvee.pure

import cuvee.sexpr
import cuvee.boogie
import cuvee.smtlib.Model

sealed trait Prop extends sexpr.Syntax with boogie.Syntax {
  def toExpr: Expr
  def rename(re: Map[Var, Var]): Prop
  def subst(su: Map[Var, Expr]): Prop
}

object Prop {
  def from(expr: Expr) = Disj.from(expr) match {
    case atom @ Atom(_, _) => atom
    // In case the expression could have been written as just a Conj,
    // we'll get the sequence {} => { conj }, extract the conj and return it:
    case Disj(Nil, Nil, conj :: Nil) => conj
    case disj => disj
  }
}

sealed trait Pos extends Prop {
  def rename(re: Map[Var, Var]): Pos
  def subst(su: Map[Var, Expr]): Pos
}

sealed trait Neg extends Prop {
  def rename(re: Map[Var, Var]): Neg
  def subst(su: Map[Var, Expr]): Neg
}

// if one decides a neg == False or a pos == True
// the outer context will collapse to that result

// atomics should not have inner propositional structure
case class Atom(expr: Expr, cex: Option[Model] = None) extends Pos with Neg {
  require(cex.isEmpty || (expr != True && expr != False), "Atoms with True / False must not carry a model")

  // def text = Printer.atom(expr)
  def bound = Set()
  def toExpr = expr
  def rename(re: Map[Var, Var]) =
    Atom(expr rename re, cex map (_ rename re))
  def subst(su: Map[Var, Expr]) =
    Atom(expr subst su)
  def sexpr = expr.sexpr
  def bexpr = cex match {
    case Some(cex) => List(expr.bexpr.mkString(""), "  counterexample: " + cex.toString)
    case None => List(expr.bexpr.mkString(""))
  }
}

object Atom {
  val t = Atom(True)
  val f = Atom(False)
}

// represents
//   forall xs. /\ {ant} ==> \/ {suc}
// or written equivalently as a big disjunction
//   forall xs. \/ {not ant}  \/  \/ {suc}
case class Disj(xs: List[Var], neg: List[Neg], pos: List[Pos])
    extends Neg
    with Expr.bind[Disj] {
  require(xs == xs.distinct)

  // def text = Printer.Disj(xs, neg, pos)
  def bound = xs.toSet
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Disj(xs rename a, neg map (_ rename re), pos map (_ rename re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Disj(xs rename a, neg map (_ subst su), pos map (_ subst su))

  def toExpr: Expr = (xs, neg) match {
    case (Nil, Nil) => Or(pos map (_.toExpr))
    case (Nil, _)   => Imp(And(neg map (_.toExpr)), Or(pos map (_.toExpr)))
    case (_, Nil)   => Forall(xs, Or(pos map (_.toExpr)))
    case _ => Forall(xs, Imp(And(neg map (_.toExpr)), Or(pos map (_.toExpr))))
  }

  def sexpr =
    List("forall", xs.asFormals, List("=>", "and" :: neg, "or" :: pos))

  def bexpr = {
    var result: List[String] = Nil
    var started: Boolean = false
    val bound =
      for (x <- xs)
        yield "|   " + x.name.toLabel + ": " + x.typ

    val assms =
      for (phi <- neg; line <- phi.bexpr)
        yield "|   " + line

    val concls =
      for (phi <- pos; line <- phi.bexpr)
        yield "|   " + line

    if (bound.nonEmpty)
      result ++= List("| forall") ++ bound

    if (assms.nonEmpty)
      result ++= List("| assume") ++ assms

    if (pos.isEmpty)
      result ++= List("| show contradiction")

    if (pos.size == 1)
      result ++= List("| show") ++ concls

    if (pos.size > 1)
      result ++= List("| show one of") ++ concls

    // 
    result = result.updated(0, result(0).patch(0, "+", 1))

    result
  }
}

// represents
//   exists xs. /\{neg}
case class Conj(xs: List[Var], neg: List[Neg])
    extends Pos
    with Expr.bind[Conj] {
  require(xs == xs.distinct)

  // def text = Printer.Conj(xs, neg)
  def bound = xs.toSet
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Conj(xs rename a, neg map (_ rename re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Conj(xs rename a, neg map (_ subst su))

  def toExpr: Expr = xs match {
    case Nil => And(neg map (_.toExpr))
    case _   => Exists(xs, And(neg map (_.toExpr)))
  }

  def sexpr =
    List("exists", xs.asFormals, "or" :: neg)

  def bexpr = {
    var result: List[String] = Nil

    val bound =
      for (x <- xs)
        yield "|   " + x.name.toLabel + ": " + x.typ

    val indent = "|   " + (if (bound.isEmpty) "" else "  ")

    val concls =
      for (phi <- neg; line <- phi.bexpr)
        yield indent + line

    if (bound.nonEmpty)
      result ++= List("| exists") ++ bound

    if (neg.size == 1)
      result ++= List("| show") ++ concls

    if (neg.size > 1)
      result ++= List("| show all of") ++ concls

    result = result.updated(0, result(0).patch(0, "+", 1))

    result
  }
}

object Disj {

//   def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
//     Simplify.forall(xs, Simplify.imp(Simplify.and(neg), Simplify.or(pos)))
//   }

  // def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
  //   Forall(xs, And(neg) ==> Or(pos))
  // }

  // def unapply(expr: Expr) = expr match {
  //   case Forall(xs, Imp(And(neg), Or(pos))) => Some((xs, neg, pos))
  //   case Imp(And(neg), Or(pos))             => Some((Nil, neg, pos))
  //   case _                                  => None
  // }

  def from(expr: Expr) =
    Disj.show(List(expr), Nil, Nil, Nil)

  def from(exprs: List[Expr]) =
    Disj.show(exprs, Nil, Nil, Nil)

  def from(xs: List[Var], neg: List[Expr], pos: List[Expr]) =
    Disj.assume(neg, pos, xs, Nil, Nil)

  def assume(
      that: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg],
      pos: List[Pos]
  ): Neg = {
    that match {
      case Nil =>
        show(todo, xs, neg, pos)
      case True :: rest =>
        assume(rest, todo, xs, neg, pos)
      case False :: rest =>
        Atom(True)
      case Not(phi) :: rest =>
        assume(rest, phi :: todo, xs, neg, pos)
      case And(phis) :: rest =>
        assume(phis ++ rest, todo, xs, neg, pos)
      case (expr @ Exists(_, _)) :: rest =>
        val Exists(ys, body) = expr refresh xs
        assume(body :: rest, todo, xs ++ ys, neg, pos)
      case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
        assume(And(Imp(phi, psi), Imp(psi, phi)) :: rest, todo, xs, neg, pos)
      case Imp(phi, psi) :: rest =>
        val prop = assume(List(phi), List(psi), Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case Or(phis) :: rest =>
        val prop = show(phis, Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case (expr @ Forall(_, _)) :: rest =>
        val prop = show(List(expr), Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case phi :: rest =>
        assume(rest, todo, xs, neg ++ List(Atom(phi)), pos)
    }
  }

  def show(
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg],
      pos: List[Pos]
  ): Neg = {
    todo match {
      case Nil if neg == Nil && pos == Nil =>
        Atom.f
      case Nil =>
        Disj(xs, neg, pos)
      case False :: rest =>
        show(rest, xs, neg, pos)
      case True :: rest =>
        Atom(True)
      case Not(phi) :: rest =>
        assume(List(phi), rest, xs, neg, pos)
      case And(phis) :: rest =>
        val prop = Conj.from(phis)
        show(rest, xs, neg, pos ++ List(prop))
      case (expr @ Exists(_, _)) :: rest =>
        Conj.from(expr) match {
          case Atom(False, _) =>
            show(rest, xs, neg, pos)
          case prop @ Atom(True, _) =>
            prop
          case prop =>
            show(rest, xs, neg, pos ++ List(prop))
        }
      case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
        show(And(Imp(phi, psi), Imp(psi, phi)) :: rest, xs, neg, pos)
      case Imp(phi, psi) :: rest =>
        assume(List(phi), psi :: rest, xs, neg, pos)
      case Or(phis) :: rest =>
        show(phis ++ rest, xs, neg, pos)
      case (expr @ Forall(_, _)) :: rest =>
        val Forall(ys, body) = expr refresh xs
        show(body :: rest, xs ++ ys, neg, pos)
      case phi :: rest =>
        show(rest, xs, neg, pos ++ List(Atom(phi)))
    }
  }

  def from(
    xs: List[Var], neg: List[Prop], pos: List[Prop]
  )(implicit s: DummyImplicit): Neg =
    Disj.assume(neg, pos, xs, Nil, Nil)

  def assume(
    that: List[Prop],
    todo: List[Prop],
    xs: List[Var],
    neg: List[Neg],
    pos: List[Pos]
  )(implicit s: DummyImplicit): Neg = {
    that match {
      case Nil =>
        show(todo, xs, neg, pos)

      case Atom(True, _) :: rest =>
        assume(rest, todo, xs, neg, pos)
      case Atom(False, _) :: rest =>
        Atom.t
      case (atom: Atom) :: rest =>
        assume(rest, todo, xs, neg ++ List(atom), pos)

      case (disj @ Disj(xs_, neg_, pos_)) :: rest =>
        assume(rest, todo, xs, neg ++ List(disj), pos)

      case (conj @ Conj(xs_, _)) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Conj(zs, neg_) = conj.rename(re)

        assume(neg_ ++ rest, todo, xs ++ zs, neg, pos)
    }
  }

  def show(
    todo: List[Prop],
    xs: List[Var],
    neg: List[Neg],
    pos: List[Pos]
  )(implicit s: DummyImplicit): Neg = {
    todo match {
      case Nil =>
        Disj(xs, neg, pos)

      case Atom(False, _) :: rest =>
        show(rest, xs, neg, pos)
      case Atom(True, _) :: rest =>
        Atom.t
      case (phi: Atom) :: rest =>
        show(rest, xs, neg, pos ++ List(phi))

      case (Conj(Nil, (disj @ Disj(xs_, _, _)) :: Nil)) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Disj(zs, neg_, pos_) = disj.rename(re)

        assume(neg_, pos_ ++ rest, zs ++ xs, neg, pos)

      case (disj @ Disj(xs_, _, _)) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Disj(zs, neg_, pos_) = disj.rename(re)

        assume(neg_, pos_ ++ rest, zs ++ xs, neg, pos)

      case (conj: Conj) :: rest =>
        show(rest, xs, neg, pos ++ List(conj))
    }
  }
}

object Conj {
  def from(expr: Expr) =
    Conj.show(List(expr), Nil, Nil)

  def from(exprs: List[Expr]) =
    Conj.show(exprs, Nil, Nil)

  def from(xs: List[Var], neg: List[Expr]) =
    Conj.show(neg, xs, Nil)

  // def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
  //   Simplify.exists(xs, Simplify.and(neg) && Simplify.and(pos map (Simplify.not(_))))
  // }

  // def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
  //   Exists(xs, And(neg ++ Not(pos)))
  // }

  // def unapply(expr: Expr) = expr match {
  //   case Exists(xs, And(e)) =>
  //     val (pos_, neg) = e partition { case Not(_) => true }
  //     val pos = pos_ collect { case Not(e) => e }
  //     Some((xs, neg, pos))
  //   case And(e) =>
  //     val (pos_, neg) = e partition { case Not(_) => true }
  //     val pos = pos_ collect { case Not(e) => e }
  //     Some((Nil, neg, pos))
  //   case _ => None
  // }

  def avoid(
      first: Neg,
      rest: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg]
  ): Pos = first match {
    case Atom(True, _) =>
      Atom(False)
    case Atom(False, _) =>
      avoid(rest, todo, xs, neg)
    case _ =>
      avoid(rest, todo, xs, neg ++ List(first))
  }

  def avoid(
      that: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg]
  ): Pos = {
    that match {
      case Nil =>
        show(todo, xs, neg)
      case False :: rest =>
        avoid(rest, todo, xs, neg)
      case True :: rest =>
        Atom(False)
      case Not(phi) :: rest =>
        avoid(rest, phi :: todo, xs, neg)
      case And(phis) :: rest =>
        val prop = Disj.assume(phis, Nil, Nil, Nil, Nil) // /\ {phis} ==> false
        avoid(prop, rest, todo, xs, neg)
      case (expr @ Exists(_, _)) :: rest =>
        val prop = Disj.assume(List(expr), Nil, Nil, Nil, Nil)
        // (exists xs. P(xs)) ==> false  ~~> (forall xs. P(xs) ==> false)
        avoid(prop, rest, todo, xs, neg)
      case Imp(phi, psi) :: rest =>
        avoid(psi :: rest, phi :: todo, xs, neg)
      case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
        avoid(And(Imp(phi, psi), Imp(psi, phi)) :: rest, todo, xs, neg)
      case Or(phis) :: rest =>
        avoid(phis ++ rest, todo, xs, neg)
      case (expr @ Forall(_, _)) :: rest =>
        val Forall(ys, body) = expr refresh xs
        avoid(body :: rest, todo, xs ++ ys, neg)
      case phi :: rest =>
        avoid(rest, todo, xs, neg ++ List(Atom(!phi)))
    }
  }

  def show(
      first: Neg,
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg]
  ): Pos = first match {
    case Atom(False, _) =>
      Atom(False)
    case Atom(True, _) =>
      show(todo, xs, neg)
    case _ =>
      show(todo, xs, neg ++ List(first))
  }

  def show(
      todo: List[Expr],
      xs: List[Var],
      neg: List[Neg]
  ): Pos = {
    todo match {
      case Nil if neg.isEmpty =>
        Atom(True)
      case Nil =>
        Conj(xs, neg)
      case True :: rest =>
        show(rest, xs, neg)
      case False :: rest =>
        Atom(False)
      case Not(phi) :: rest =>
        avoid(List(phi), rest, xs, neg)
      case And(phis) :: rest =>
        show(phis ++ rest, xs, neg)
      case (expr @ Exists(_, _)) :: rest =>
        val Exists(ys, body) = expr refresh xs
        show(body :: rest, xs ++ ys, neg)
      case Imp(phi, psi) :: rest =>
        val prop = Disj.assume(List(phi), List(psi), Nil, Nil, Nil)
        show(prop, rest, xs, neg)
      case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
        show(Imp(phi, psi) :: Imp(psi, phi) :: rest, xs, neg)
      case Or(phis) :: rest =>
        val prop = Disj.show(phis, Nil, Nil, Nil)
        show(prop, rest, xs, neg)
      case (expr @ Forall(_, _)) :: rest =>
        val prop = Disj.show(List(expr), Nil, Nil, Nil)
        show(rest, xs, neg ++ List(prop))
      case phi :: rest =>
        show(rest, xs, neg ++ List(Atom(phi)))
    }
  }

  def from(
    xs: List[Var], neg: List[Prop]
  )(implicit s: DummyImplicit): Pos =
    Conj.show(neg, xs, Nil)

  def avoid(
      first: Neg,
      rest: List[Prop],
      todo: List[Prop],
      xs: List[Var],
      neg: List[Neg]
  )(implicit s: DummyImplicit): Pos = first match {
    case Atom.t =>
      Atom.f
    case Atom.f =>
      avoid(rest, todo, xs, neg)
    case _ =>
      avoid(rest, todo, xs, neg ++ List(first))
  }

  def avoid(
      that: List[Prop],
      todo: List[Prop],
      xs: List[Var],
      neg: List[Neg]
  )(implicit s: DummyImplicit): Pos = {
    that match {
      case Nil =>
        show(todo, xs, neg)

      case Atom.f :: rest =>
        avoid(rest, todo, xs, neg)
      case Atom.t :: rest =>
        Atom.f

      case (phi: Atom) :: rest =>
        // !phi = phi ==> False = Disj([], [phi], [])
        val nphi = Disj.from(Nil, List(phi), Nil)
        avoid(rest, todo, xs, neg ++ List(nphi))

      case (disj @ Disj(xs_, _, _)) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Disj(zs, neg_, pos_) = disj.rename(re)
        avoid(pos_ ++ rest, neg_ ++ todo, xs ++ zs, neg)

      case (conj: Conj) :: rest =>
        val prop = Disj.assume(List(conj), Nil, Nil, Nil, Nil)
        avoid(prop, rest, todo, xs, neg)
    }
  }

  def show(
      first: Neg,
      todo: List[Prop],
      xs: List[Var],
      neg: List[Neg]
  )(implicit s: DummyImplicit): Pos = first match {
    case Atom.f =>
      Atom.f
    case Atom.t =>
      show(todo, xs, neg)
    case _ =>
      show(todo, xs, neg ++ List(first))
  }

  def show(
      todo: List[Prop],
      xs: List[Var],
      neg: List[Neg]
  )(implicit s: DummyImplicit): Pos = {
    todo match {
      case Nil if neg.isEmpty =>
        Atom.t

      case Nil =>
        Conj(xs, neg)

      case Atom.t :: rest =>
        show(rest, xs, neg)
      case Atom.f :: rest =>
        Atom.f
      case (atom: Atom) :: rest =>
        show(rest, xs, neg ++ List(atom))


      case Disj(Nil, Nil, (conj @ Conj(xs_, _)) :: Nil) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Conj(zs, neg_) = conj.rename(re)

        show(neg_ ++ rest, xs ++ zs, neg)

      case (conj @ Conj(xs_, _)) :: rest =>
        val ys = xs intersect xs_
        val re = Expr.fresh(ys)

        val Conj(zs, neg_) = conj.rename(re)

        show(neg_ ++ rest, xs ++ zs, neg)


      case (disj: Disj) :: rest =>
        show(disj, rest, xs, neg)
    }
  }
}

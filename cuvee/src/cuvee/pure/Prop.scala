package cuvee.pure

// sealed trait Prop extends Pretty {
//   def toExpr: Expr
// }

// sealed trait Pos extends Prop
// sealed trait Neg extends Prop

// if one decides a neg == False or a pos == True
// the outer context will collapse to that result

// atomics should not have inner propositional structure
// case class Atom(expr: Expr) extends Pos with Neg {
//   def text = Printer.atom(expr)
//   def unary_! = Atom(!expr)
//   def toExpr = expr
// }

// object Atom {
//   val t = Atom(True)
//   val f = Atom(False)
// }

// represents
//   forall xs. /\{ant} ==> \/ suc
// or written equivalently as a big disjunction
//   forall xs. \/{not ant}  \/  \/{suc}
// case class Disj(xs: List[Var], neg: List[Neg], pos: List[Pos]) extends Neg {
//   def text = Printer.Disj(xs, neg, pos)
//   def toExpr = Forall(xs, And(neg map (_.toExpr)) ==> Or(pos map (_.toExpr)))
// }

// represents
//   exists xs. /\{neg} /\ /\{not pos}
// case class Conj(xs: List[Var], neg: List[Neg], pos: List[Pos]) extends Pos {
//   def text = Printer.Conj(xs, neg, pos)
//   def toExpr = Forall(xs, And(neg map (_.toExpr)) && And(pos map (!_.toExpr)))
// }

object Disj {

//   def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
//     Simplify.forall(xs, Simplify.imp(Simplify.and(neg), Simplify.or(pos)))
//   }

  def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
    Forall(xs, And(neg) ==> Or(pos))
  }

  def unapply(expr: Expr) = expr match {
    case Forall(xs, Imp(And(neg), Or(pos))) => Some((xs, neg, pos))
    case Imp(And(neg), Or(pos))             => Some((Nil, neg, pos))
    case _                                  => None
  }

  def assume(
      that: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      neg: List[Expr],
      pos: List[Expr]
  ): Expr = {
    that match {
      case Nil =>
        show(todo, xs, neg, pos)
      case Not(phi) :: rest =>
        assume(rest, phi :: todo, xs, neg, pos)
      case And(phis) :: rest =>
        assume(phis ++ rest, todo, xs, neg, pos)
      case (expr @ Exists(_, _)) :: rest =>
        val Exists(ys, body) = expr refresh xs
        assume(body :: rest, todo, xs ++ ys, neg, pos)
      case Imp(phi, psi) :: rest =>
        val prop = Disj.assume(List(phi), List(psi), Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case Or(phis) :: rest =>
        val prop = show(phis, Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case (expr @ Forall(_, _)) :: rest =>
        val prop = Disj.show(List(expr), Nil, Nil, Nil)
        assume(rest, todo, xs, neg ++ List(prop), pos)
      case phi :: rest =>
        assume(rest, todo, xs, neg ++ List(phi), pos)
    }
  }

  def show(
      todo: List[Expr],
      xs: List[Var],
      neg: List[Expr],
      pos: List[Expr]
  ): Expr = {
    todo match {
      case Nil =>
        Disj(xs, neg, pos)
      case Not(phi) :: rest =>
        assume(List(phi), rest, xs, neg, pos)
      case And(phis) :: rest =>
        val prop = Conj.show(phis, Nil, Nil, Nil)
        show(rest, xs, neg, pos ++ List(prop))
      case (expr @ Exists(_, _)) :: rest =>
        val prop = Conj.show(List(expr), Nil, Nil, Nil)
        show(rest, xs, neg, pos ++ List(prop))
      case Imp(phi, psi) :: rest =>
        assume(List(phi), psi :: rest, xs, neg, pos)
      case Or(phis) :: rest =>
        show(phis ++ rest, xs, neg, pos)
      case (expr @ Forall(_, _)) :: rest =>
        val Forall(ys, body) = expr refresh xs
        show(body :: rest, xs ++ ys, neg, pos)
      case phi :: rest =>
        show(rest, xs, neg, pos ++ List(phi))
    }
  }
}

object Conj {

//   def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
//     Simplify.exists(xs, Simplify.and(neg) && Simplify.and(pos map (Simplify.not(_))))
//   }

  def apply(xs: List[Var], neg: List[Expr], pos: List[Expr]) = {
    Exists(xs, And(neg ++ Not(pos)))
  }

  def unapply(expr: Expr) = expr match {
    case Exists(xs, And(e)) =>
      val (pos_, neg) = e partition { case Not(_) => true }
      val pos = pos_ collect { case Not(e) => e }
      Some((xs, neg, pos))
    case And(e) =>
      val (pos_, neg) = e partition { case Not(_) => true }
      val pos = pos_ collect { case Not(e) => e }
      Some((Nil, neg, pos))
    case _ => None
  }

  def avoid(
      that: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      neg: List[Expr],
      pos: List[Expr]
  ): Expr = {
    that match {
      case Nil =>
        show(todo, xs, neg, pos)
      case Not(phi) :: rest =>
        avoid(rest, phi :: todo, xs, neg, pos)
      case And(phis) :: rest =>
        val prop = Conj.show(phis, Nil, Nil, Nil)
        avoid(rest, todo, xs, neg, pos ++ List(prop))
      case (expr @ Exists(_, _)) :: rest =>
        val prop = Conj.show(List(expr), Nil, Nil, Nil)
        avoid(rest, todo, xs, neg, pos ++ List(prop))
      case Imp(phi, psi) :: rest =>
        avoid(psi :: rest, phi :: todo, xs, neg, pos)
      case Or(phis) :: rest =>
        avoid(phis ++ rest, todo, xs, neg, pos)
      case (expr @ Forall(_, _)) :: rest =>
        val Forall(ys, body) = expr refresh xs
        avoid(body :: rest, todo, xs ++ ys, neg, pos)
      case phi :: rest =>
        avoid(rest, todo, xs, neg, pos ++ List(phi))
    }
  }

  def show(
      todo: List[Expr],
      xs: List[Var],
      neg: List[Expr],
      pos: List[Expr]
  ): Expr = {
    todo match {
      case Nil =>
        Conj(xs, neg, pos)
      case Not(phi) :: rest =>
        avoid(List(phi), rest, xs, neg, pos)
      case And(phis) :: rest =>
        show(phis ++ rest, xs, neg, pos)
      case (expr @ Exists(_, _)) :: rest =>
        val Exists(ys, body) = expr refresh xs
        show(body :: rest, xs ++ ys, neg, pos)
      case Imp(phi, psi) :: rest =>
        val prop = Disj.assume(List(phi), List(psi), Nil, Nil, Nil)
        show(rest, xs, neg ++ List(prop), pos)
      case Or(phis) :: rest =>
        val prop = Disj.show(phis, Nil, Nil, Nil)
        show(rest, xs, neg ++ List(prop), pos)
      case (expr @ Forall(_, _)) :: rest =>
        val prop = Disj.show(List(expr), Nil, Nil, Nil)
        show(rest, xs, neg ++ List(prop), pos)
      case phi :: rest =>
        show(rest, xs, neg ++ List(phi), pos)
    }
  }
}

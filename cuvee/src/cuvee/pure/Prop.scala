package cuvee.pure

import cuvee.util
import cuvee.smtlib.Model

sealed trait Prop extends util.Syntax {
  def isTrue: Boolean
  def toExpr: Expr
  def rename(re: Map[Var, Var]): Prop
  def subst(su: Map[Var, Expr]): Prop

  def map(f: Atom => Prop): Prop =
    this match {
      case atom @ Atom(phi, cex) =>
        f(atom)
      case Disj(xs, assms, concls) =>
        Disj(xs, assms map (_ map f), concls map (_ map f))
    }
}

object Prop {
  def from(expr: Expr): Prop =
    from(Nil, Nil, List(expr))

  // def from(exprs: List[Expr]): Prop =
  //   from(Nil, Nil, exprs)

  def from(xs: List[Var], pre: List[Expr], post: List[Expr]): Prop =
    from(pre, post, xs, Nil, Nil)

  def from(
      pre: List[Expr],
      post: List[Expr],
      xs: List[Var],
      assms: List[Prop],
      concls: List[Conj]
  ): Prop = {
    pre match {
      case Nil =>
        from(post, xs, assms, concls)

      case True :: rest =>
        from(rest, post, xs, assms, concls)

      case False :: rest =>
        Atom.t

      case Note(phi, _) :: rest =>
        from(phi :: rest, post, xs, assms, concls)

      case Not(phi) :: rest =>
        from(rest, phi :: post, xs, assms, concls)

      case And(phis) :: rest =>
        from(phis ++ rest, post, xs, assms, concls)

      case (expr @ Exists(_, _)) :: rest =>
        val Exists(ys, body) = expr refresh xs
        from(body :: rest, post, xs ++ ys, assms, concls)

      // case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
      //   from(And(Imp(phi, psi), Imp(psi, phi)) :: rest, post, xs, assms, concls)

      case Imp(phi, psi) :: rest =>
        val prop = from(List(phi), List(psi), Nil, Nil, Nil)
        from(rest, post, xs, assms ++ List(prop), concls)

      case Or(phis) :: rest =>
        val prop = from(phis, Nil, Nil, Nil)
        from(rest, post, xs, assms ++ List(prop), concls)

      case (phi @ Forall(_, _)) :: rest =>
        val prop = from(phi)
        from(rest, post, xs, assms ++ List(prop), concls)

      case phi :: rest =>
        from(rest, post, xs, assms ++ List(Atom(phi)), concls)
    }
  }

  def from(
      post: List[Expr],
      xs: List[Var],
      assms: List[Prop],
      concls: List[Conj]
  ): Prop = {
    post match {
      case Nil =>
        (xs, assms, concls) match {
          case (Nil, Nil, Nil) =>
            Atom.f
          case (Nil, Nil, List(Conj(Nil, List(Disj(ys, assms, concls))))) =>
            Disj(xs ++ ys, assms, concls)
          case _ =>
            Disj(xs, assms, concls)
        }

      case False :: rest =>
        from(rest, xs, assms, concls)

      case True :: rest =>
        Atom.t

      case Note(phi, _) :: rest =>
        from(phi :: rest, xs, assms, concls)

      case Not(phi) :: rest =>
        from(List(phi), rest, xs, assms, concls)

      // case Eq(phi, psi) :: rest if phi.typ == Sort.bool =>
      //   show(And(Imp(phi, psi), Imp(psi, phi)) :: rest, xs, assms, concls)

      case Imp(phi, psi) :: rest =>
        from(List(phi), psi :: rest, xs, assms, concls)

      case Or(phis) :: rest =>
        from(phis ++ rest, xs, assms, concls)

      case (expr @ Forall(_, _)) :: rest =>
        val Forall(ys, body) = expr refresh xs
        from(body :: rest, xs ++ ys, assms, concls)

      case (let @ Let(_, _)) :: rest =>
        val Let(eqs, body) = let refresh xs
        val (keep, inline) = eqs partition { case LetEq(x, e) =>
          e.free contains x
        }

        val ys = keep map (_.x)
        val phis = keep map (_.toEq)

        val su = inline map { case LetEq(x, e) =>
          (x, e)
        }

        val body_ = body subst su.toMap
        from(phis, body_ :: rest, xs ++ ys, assms, concls)

      // case And(phis) :: rest =>
      //   val prop = Conj.from(phis)
      //   from(rest, xs, assms, concls ++ List(prop))
      // case (expr @ Exists(_, _)) :: rest =>
      //   Conj.from(expr) match {
      //     case Atom(False, _) =>
      //       show(rest, xs, assms, concls)
      //     case prop @ Atom(True, _) =>
      //       prop
      //     case prop =>
      //       from(rest, xs, assms, concls ++ List(prop))
      //   }

      case phi :: rest =>
        Conj.from(phi) match {
          case Conj(_, Nil) =>
            Atom.t

          case Conj(_, List(Atom(False, _))) =>
            from(rest, xs, assms, concls)

          case concl =>
            from(rest, xs, assms, concls ++ List(concl))
        }
    }
  }
}

// atomics should not have inner conclusion structure
case class Atom(phi: Expr, cex: Option[Model] = None) extends Prop {
  require(phi.typ == Sort.bool, "not a boolean conclusion: " + phi)
  // require(cex.isEmpty || (expr != True && expr != False), "Atoms with True / False must not carry a model")

  phi match {
    case Not(_) | And(_) | Or(_) | Imp(_, _) =>
      cuvee.error("invalid atom: " + phi)
    case Bind(_, _, _, _) =>
      cuvee.error("invalid atom: " + phi)
    case _ =>
  }

  def isTrue: Boolean = (phi == True)
  // def text = Printer.atom(expr)
  def bound = Set()
  def toExpr = phi
  def rename(re: Map[Var, Var]) =
    Atom(phi rename re, cex map (_ rename re))
  def subst(su: Map[Var, Expr]) =
    Atom(phi subst su)
}

object Atom {
  val t = Atom(True)
  val f = Atom(False)
}

// represents
//   forall xs. /\ {ant} ==> \/ {suc}
// or written equivalently as a big disjunction
//   forall xs. \/ {not ant}  \/  \/ {suc}
case class Disj(xs: List[Var], assms: List[Prop], concls: List[Conj])
    extends Prop
    with Expr.bind[Disj] {
  require(xs == xs.distinct, "duplicate vars in " + xs)

  def isTrue = false
  def bound = xs.toSet
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Disj(xs rename a, assms map (_ rename re), concls map (_ rename re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Disj(xs rename a, assms map (_ subst su), concls map (_ subst su))

  def toExpr: Expr = (xs, assms) match {
    case (Nil, Nil) => Or(concls map (_.toExpr))
    case (Nil, _)   => Imp(And(assms map (_.toExpr)), Or(concls map (_.toExpr)))
    case (_, Nil)   => Forall(xs, Or(concls map (_.toExpr)))
    case _          => Forall(xs, Imp(And(assms map (_.toExpr)), Or(concls map (_.toExpr))))
  }
}

// represents
//   exists xs. /\ {props}
case class Conj(xs: List[Var], props: List[Prop]) extends Expr.bind[Conj] {
  require(xs == xs.distinct)

  def map(f: Atom => Prop): Conj =
    Conj(xs, props map (_ map f))

  def bound = xs.toSet
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Conj(xs rename a, props map (_ rename re))
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Conj(xs rename a, props map (_ subst su))

  def toExpr: Expr = xs match {
    case Nil => And(props map (_.toExpr))
    case _   => Exists(xs, And(props map (_.toExpr)))
  }
}

object Disj {
  def reduce(xs: List[Var], assms: List[Prop], concls: List[Conj]): Prop =
    reduce(assms, concls, xs, Nil, Nil)

  def reduce(
      pre: List[Prop],
      post: List[Conj],
      xs: List[Var],
      assms: List[Prop],
      concls: List[Conj]
  ): Prop = {
    pre match {
      case Nil =>
        reduce(post, xs, assms, concls)

      case Atom(False, _) :: rest =>
        Atom.t

      case Atom(True, _) :: rest =>
        reduce(rest, post, xs, assms, concls)

      case Disj(Nil, Nil, List(conj)) :: rest =>
        val Conj(ys, props) = conj refresh xs
        reduce(props ++ rest, post, xs ++ ys, assms, concls)

      case prop :: rest =>
        reduce(rest, post, xs, assms ++ List(prop), concls)
    }
  }

  def reduce(
      post: List[Conj],
      xs: List[Var],
      assms: List[Prop],
      concls: List[Conj]
  ): Prop = {
    post match {
      case Nil =>
        (assms, concls) match {
          case (Nil, Nil) =>
            Atom.f
          case (Nil, List(Conj(Nil, List(Disj(ys, assms, concls))))) =>
            Disj(xs ++ ys, assms, concls)
          case _ =>
            Disj(xs, assms, concls)
        }

      case Conj(_, Nil) :: rest =>
        Atom.t

      case Conj(_, List(Atom(False, _))) :: rest =>
        reduce(rest, xs, assms, concls)

      case conj :: rest =>
        reduce(rest, xs, assms, concls ++ List(conj))
    }
  }
}

object Conj {
  val t = Conj(Nil, Nil)
  val f = Conj(Nil, List(Atom.f))

  def from(expr: Expr): Conj =
    from(Nil, List(expr))

  def from(xs: List[Var], exprs: List[Expr]): Conj =
    from(exprs, xs, Nil)

  def from(
      pos: List[Expr],
      xs: List[Var],
      props: List[Prop]
  ): Conj = pos match {
    case Nil =>
      props match {
        case Nil =>
          Conj.t

        case List(Disj(Nil, Nil, List(conj))) =>
          conj

        case _ =>
          Conj(xs, props)
      }

    case False :: rest =>
      Conj.f

    case True :: rest =>
      from(rest, xs, props)

    case Note(phi, _) :: rest =>
      from(phi :: rest, xs, props)

    case Not(phi) :: rest =>
      from(List(phi), rest, xs, props)

    case And(phis) :: rest =>
      from(phis ++ rest, xs, props)

    case (expr @ Exists(_, _)) :: rest =>
      val Exists(ys, body) = expr refresh xs
      from(body :: rest, xs ++ ys, props)

    case (phi @ (Imp(_, _) | Or(_) | Forall(_, _))) :: rest =>
      Prop.from(phi) match {
        case Atom(False, _) =>
          Conj.f

        case Atom(True, _) =>
          from(rest, xs, props)

        case prop =>
          from(rest, xs, props ++ List(prop))
      }

    case phi :: rest =>
      from(rest, xs, props ++ List(Atom(phi)))
  }

  def from(
      neg: List[Expr],
      pos: List[Expr],
      xs: List[Var],
      props: List[Prop]
  ): Conj = neg match {
    case Nil =>
      from(pos, xs, props)

    case True :: rest =>
      Conj.f

    case False :: rest =>
      from(rest, pos, xs, props)

    case Note(phi, _) :: rest =>
      from(phi :: rest, pos, xs, props)

    case Not(phi) :: rest =>
      from(rest, phi :: pos, xs, props)

    case Or(phis) :: rest =>
      from(phis ++ rest, pos, xs, props)

    case Imp(phi, psi) :: rest =>
      from(psi :: rest, phi :: pos, xs, props)

    case (expr @ Forall(_, _)) :: rest =>
      val Forall(ys, body) = expr refresh xs
      from(body :: rest, xs ++ ys, props)

    case (phi @ (And(_) | Exists(_, _))) :: rest =>
      Prop.from(!phi) match {
        case Atom(False, _) =>
          Conj.f

        case Atom(True, _) =>
          from(rest, xs, props)

        case prop =>
          from(rest, xs, props ++ List(prop))
      }

    case phi :: rest =>
      from(rest, xs, props ++ List(Atom(phi)))
  }

  def reduce(xs: List[Var], props: List[Prop]): Conj =
    reduce(props, xs, Nil)

  def reduce(
      pos: List[Prop],
      xs: List[Var],
      props: List[Prop]
  ): Conj = pos match {
    case Nil =>
      props match {
        case Nil =>
          Conj.t
        case List(Disj(Nil, Nil, List(conj))) =>
          conj
        case _ =>
          Conj(xs, props)
      }

    case Atom(False, _) :: rest =>
      Conj.f

    case Atom(True, _) :: rest =>
      reduce(rest, xs, props)

    case Disj(Nil, Nil, List(conj)) :: rest =>
      val Conj(ys, add) = conj refresh xs
      reduce(add ++ rest, xs ++ ys, props)

    case prop :: rest =>
      reduce(rest, xs, props ++ List(prop))
  }
}

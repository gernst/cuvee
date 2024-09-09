package cuvee.pure

import cuvee.pipe.Stage
import cuvee.State
import cuvee.smtlib.Cmd
import cuvee.smtlib.Lemma

object Horn extends Stage {

  override def exec(
      prefix: List[Cmd],
      cmds: List[Cmd],
      last: Cmd,
      in: State
  ): List[Cmd] = {
    cmds flatMap {
      case Lemma(todo, None, flag, named) =>
        val goals = assert(List(todo), Nil, Nil, Nil)
        goals.distinct map {
          case Clause(xs, ant, Note(expr, attr)) =>
            Lemma(Clause(xs, ant, expr), None, flag, named ++ attr)
          case expr =>
            Lemma(expr, None, flag, named)
        }

      case cmd =>
        List(cmd)
    }
  }

  def assert(
      todo: List[Expr],
      xs: List[Var],
      ant: List[Expr],
      suc: List[Expr]
  ): List[Expr] = {
    todo match {
      case Nil =>
        List(Clause(xs, ant, Or(suc)))

      case True :: rest =>
        Nil

      case False :: rest =>
        assert(rest, xs, ant, suc)

      case Not(phi) :: rest =>
        assume(List(phi), rest, xs, ant, suc)

      case Imp(phi, psi) :: rest =>
        assume(List(phi), psi :: rest, xs, ant, suc)

      case Note(Imp(phi, psi), attr) :: rest =>
        assume(List(phi), Note(psi, attr) :: rest, xs, ant, suc)

      case Or(exprs) :: rest =>
        assert(exprs ++ rest, xs, ant, suc)

      case And(exprs) :: rest =>
        for (
          expr <- exprs;
          clause <- assert(expr :: rest, xs, ant, suc)
        )
          yield clause

      case Note(And(exprs), attr) :: rest =>
        for (
          expr <- exprs;
          clause <- assert(Note(expr, attr) :: rest, xs, ant, suc)
        )
          yield clause

      case (expr @ Forall(_, _)) :: rest =>
        val Forall(bound, body) = expr refresh xs
        assert(body :: rest, xs ++ bound, ant, suc)

      case Note(expr @ Forall(_, _), attr) :: rest =>
        val Forall(bound, body) = expr refresh xs
        assert(Note(body, attr) :: rest, xs ++ bound, ant, suc)

      case phi :: rest =>
        assert(rest, xs, ant, suc ++ List(phi))
    }
  }

  def assume(
      that: List[Expr],
      todo: List[Expr],
      xs: List[Var],
      ant: List[Expr],
      suc: List[Expr]
  ): List[Expr] = {
    that match {
      case Nil =>
        assert(todo, xs, ant, suc)

      case True :: rest =>
        assume(rest, todo, xs, ant, suc)

      case False :: rest =>
        Nil

      // case Not(phi) :: rest =>
      //   assume(rest, phi :: todo, xs, ant, suc)

      case Not(Not(phi)) :: rest =>
        assume(phi :: rest, todo, xs, ant, suc)

      case Not(Imp(phi, psi)) :: rest =>
        assume(!phi :: psi :: rest, todo, xs, ant, suc)

      case Not(Or(phis)) :: rest =>
        assume(And(phis map Not) :: rest, todo, xs, ant, suc)

      case Not(And(phis)) :: rest =>
        assume(Or(phis map Not) :: rest, todo, xs, ant, suc)

      case Not(Exists(bound, body)) :: rest =>
        assume(Forall(bound, !body) :: rest, todo, xs, ant, suc)

      case Or(exprs) :: rest =>
        for (
          expr <- exprs;
          clause <- assume(expr :: rest, todo, xs, ant, suc)
        )
          yield clause

      case And(exprs) :: rest =>
        assume(exprs ++ rest, todo, xs, ant, suc)

      //   case Eq(x: Id, right) :: rest if !(right.free contains x) && (xs.ids contains x) =>
      //     val _xs = xs filterNot (_.id == x)
      //     val su = Map(x -> right)
      //     val _rest = rest map (_ subst su)
      //     val _todo = todo map (_ subst su)
      //     val _ant = ant map (_ subst su)
      //     val _suc = suc map (_ subst su)
      //     assume(_rest, _todo, _xs, _ant, _suc)

      //   case Eq(right, x: Id) :: rest if !(right.free contains x) && (xs.ids contains x) =>
      //     val _eq = Eq(x, right)
      //     assume(_eq :: rest, todo, xs, ant, suc)

      case (expr @ Exists(bound, body)) :: rest =>
        val Exists(bound, body) = expr refresh xs
        assume(body :: rest, todo, xs ++ bound, ant, suc)

      //   case Distinct(List(x: Id, Id("nil", None))) :: rest if false =>
      //     // common case, introduce a cons cell here
      //     val y = Id("y")
      //     val ys = Id("ys")
      //     val (List(elem, list), _) = st.funs(Id("cons"))
      //     val fresh = List(Formal(y, elem), Formal(ys, list))
      //     val eq = Exists(fresh, x === App(Id("cons"), List(y, ys)))
      //     assume(eq :: that, todo, xs, ant, suc)

      case phi :: rest =>
        assume(rest, todo, xs, ant ++ List(phi), suc)
    }
  }

  def cases(expr: Expr): List[Expr] = expr match {
    case App(inst, args) =>
      args flatMap cases

    case Select(Store(base, index, value), index_) =>
      List(index === index_)

    case _ =>
      Nil
  }
}

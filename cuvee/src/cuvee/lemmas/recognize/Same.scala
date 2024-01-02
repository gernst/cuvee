package cuvee.lemmas.recognize

import cuvee.pure._
import cuvee.lemmas.Def
import cuvee.lemmas.C

object Same {
  import cuvee.util.Matching

  object NotAlphaEquiv extends Exception

  def isAlphaEquiv(expr1: Expr, expr2: Expr, su: Map[Var, Var]): Map[Var, Var] =
    (expr1, expr2) match {
      case (x: Var, y: Var) if (su contains x) && su(x) == y =>
        su
      case (x: Var, y: Var) if !(su contains x) =>
        su + (x -> y)

      case (Lit(any1, typ1), Lit(any2, typ2)) if any1 == any2 && typ1 == typ2 =>
        su

      case (App(inst1, args1), App(inst2, args2)) if inst1.fun == inst2.fun =>
        isAlphaEquiv(args1, args2, su)

      case _ =>
        throw NotAlphaEquiv

    }

  def isAlphaEquiv(exprs1: List[Expr], exprs2: List[Expr], su: Map[Var, Var]): Map[Var, Var] =
    (exprs1, exprs2) match {
      case (Nil, Nil) =>
        su

      case (expr1 :: rest1, expr2 :: rest2) =>
        isAlphaEquiv(expr1, expr2, isAlphaEquiv(rest1, rest2, su))
    }

  def known(df: Def, args: List[Expr], dg: Def): Option[List[Expr]] = {
    val noParams = df.params.isEmpty && dg.params.isEmpty // currently not supported
    val sameType = df.typ == dg.typ
    val sameArity = df.arity == dg.arity

    if (noParams && sameType && sameArity) {
      val is = List(0 until df.arity: _*)
      val js = List(0 until dg.arity: _*)
      assert(is.length == js.length)

      val Def(f, fcases) = df
      val Def(g, gcases) = dg

      type S = Map[(Int, Int), Map[Var, Var]]

      def checkPat(i: Int, j: Int, a: (C, Int), b: (C, Int), st: S): List[(Unit, S)] = try {
        val (cf, kf) = a
        val (cg, kg) = b
        val su = st(kf, kg)
        val su_ = isAlphaEquiv(cf.args(i), cg.args(j), su)
        val st_ = st + ((kf, kg) -> su_)
        List(((), st_))
      } catch {
        case NotAlphaEquiv =>
          Nil
      }

      def checkPats(i: Int, j: Int, st: S): List[((Int, Int), S)] = {
        val as = fcases.zipWithIndex
        val bs = gcases.zipWithIndex
        for ((_, Nil, Nil, st_) <- Matching.relate(as, bs, st, checkPat(i, j, _, _, _)))
          yield ((i, j), st_)
      }

      val init =
        for (
          kf <- 0 until fcases.length;
          kg <- 0 until gcases.length
        )
          yield (kf, kg) -> Map[Var, Var]()

      for ((map, Nil, Nil, fin) <- Matching.relate(is, js, init.toMap, checkPats(_, _, _))) {
        val perm = map.sortBy(_._1).map(_._2)
      }

      ???
    } else {
      None
    }
  }
}

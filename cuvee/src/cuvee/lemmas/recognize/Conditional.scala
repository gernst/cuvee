package cuvee.lemmas.recognize

import cuvee.pure._
import cuvee.lemmas._

import cuvee.util.Name
import scala.collection.mutable.ListBuffer

object Conditional {
  def checkIdentityWithParamPicksAndGuard(df: Def): List[(Rule, Def)] = {
    var Def(f, cases) = df
    var Fun(name, _, args, res) = f

    val results =
      for (
        (arg, n) <- args.zipWithIndex if arg == res;
        res <- checkCasesAgainstIdentAtAndGeneratePre(cases, n, f)
      )
        yield res

    return results
  }

  def checkCasesAgainstIdentAtAndGeneratePre(
      cases: List[C],
      pos: Int,
      recfunc: Fun
  ): Option[(Rule, Def)] = {
    var Fun(recfuncname, recfuncparams, recfuncargs, recfuncret) = recfunc
    var prefun = Fun(Name(recfuncname + "_id?", Some(pos)), recfuncparams, recfuncargs, Sort.bool)

    var stuff =
      for (c @ C(caseargs, caseguard, casebody) <- cases)
        yield checkCaseAgainstIdentAt(c, pos, recfunc) match {
          // case (false,Nil) => false
          case None =>
            (0, 0, C(caseargs, caseguard, False))

          case Some(recarglists) =>
            val recs = recarglists map (App(prefun, _))
            val rec = if (c.isRecursive(recfunc)) 1 else 0
            (1 - rec, rec, C(caseargs, caseguard, And(recs)))
        }

    val (base, recs, precases) = stuff.unzip3
    val nbase = base.sum
    val nrecs = recs.sum

    if (nbase > 0 && nrecs > 0) {
      val xs = Expr.vars("x", recfuncargs)
      val cond = App(prefun, xs)
      val lhs = App(recfunc, xs)
      val rhs = xs(pos)
      val eq = Rule(lhs, rhs, cond)
      val defpre = Def(prefun, precases.toList)
      Some((eq, defpre))
    } else {
      None
    }
  }

  def checkCaseAgainstIdentAt(c: C, pos: Int, recfunc: Fun): Option[List[List[Expr]]] = {
    val C(args, guard, body) = c
    val argPick = args(pos)

    argPick match {
      case arg: Var if arg == body =>
        Some(Nil) // ok but no recursive arguments

      case arg: Lit if arg == body =>
        Some(Nil)

      case App(f, pAppParamList) =>
        body match {
          case App(g, bAppParamList) if f == g => {
            val stuff = (pAppParamList zip bAppParamList) map {
              case (pAppParam: Var, bAppParam) if pAppParam == bAppParam =>
                true -> None
              case (pAppParam: Lit, bAppParam) if pAppParam == bAppParam =>
                true -> None
              case (pAppParam: Var, App(Inst(`recfunc`, _), recargs))
                  if pAppParam == recargs(pos) =>
                true -> Some(recargs)
              case (pAppParam: Lit, App(Inst(`recfunc`, _), recargs))
                  if pAppParam == recargs(pos) =>
                true -> Some(recargs)
              case other =>
                false -> None
            }

            val (oks, recargs) = stuff.unzip
            if (oks forall (b => b)) {
              Some(recargs.flatten)
            } else {
              None
            }
          }

          case other =>
            None
        }

      case other =>
        None
    }
  }

  def checkIsDefConstant(df: Def): Option[(Rule, Def)] = {
    var Def(f, cases) = df
    checkCasesAsConstantAndGeneratePre(cases, f, df.staticArgs)
  }

  def checkCasesAsConstantAndGeneratePre(
      cases: List[C],
      recfunc: Fun,
      static: List[Int]
  ): Option[(Rule, Def)] = {
    var Fun(recfuncname, recfuncparams, recfuncargs, recfuncret) = recfunc
    var prefun = Fun(Name(recfuncname + "_const?"), recfuncparams, recfuncargs, Sort.bool)

    val xs = Expr.vars("x", recfuncargs)
    val bs = static map xs

    var recNrecPreCaseConstPart =
      for (c @ C(caseargs, caseguard, casebody) <- cases)
        yield checkCaseAsConstant(c, recfunc, static, bs) match {
          case (Some(Nil), Some(constpart)) =>
            ((true, false), C(caseargs, caseguard, True), Some(constpart))
          case (Some(recargs), None) =>
            val reccall = App(prefun, recargs)
            ((false, true), C(caseargs, caseguard, reccall), None)
          case other =>
            ((false, false), C(caseargs, caseguard, False), None)
        }
    val (baserecs, precases, constparts) = recNrecPreCaseConstPart.unzip3
    val (base, recs) = baserecs.unzip
    val nbase = base.count(b => b)
    val nrecs = recs.count(b => b)

    val constpart = constparts.flatten

    constpart.distinct match {
      case List(arg) =>
        if (nbase > 0 && nrecs > 0) {
          val cond = App(prefun, xs)
          val lhs = App(recfunc, xs)
          val rhs = arg
          val eq = Rule(lhs, rhs, cond)
          val defpre = Def(prefun, precases)
          Some((eq, defpre))
        } else {
          None
        }
      case other => None
    }
  }

  def checkCaseAsConstant(
      c: C,
      recfunc: Fun,
      static: List[Int],
      recargsToStatic: List[Var]
  ): (Option[List[Expr]], Option[Expr]) = {

    val isConstantRecArgsConstPart = c match {
      case c @ C(args, guard, App(Inst(`recfunc`, _), recargs)) =>
        true -> (Some(recargs), None)
      case c @ C(args, guard, body) if !c.isRecursive(recfunc) =>
        val xs = body.free
        val as = static map args
        val ys = as.free

        val re = Expr.subst(as map { case x: Var => x }, recargsToStatic)
        val constPart = body subst re
        if (xs subsetOf ys) {
          true -> (Some(Nil), Some(constPart))
        } else {
          false -> (None, None)
        }
      case other => false -> (None, None)
    }

    val (isConstant, (recargs, constPart)) = isConstantRecArgsConstPart
    if (isConstant) {
      (recargs, constPart)
    } else {
      (None, None)
    }
  }
}

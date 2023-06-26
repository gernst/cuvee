package cuvee.lemmas

import cuvee.pure._
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
            (false, false, C(caseargs, caseguard, False))

          case Some(recarglists) =>
            val recs = recarglists map (App(prefun, _))
            val rec = c.isRecursive(recfunc)
            (!rec, rec, C(caseargs, caseguard, And(recs)))
        }

    val (base, recs, precases) = stuff.unzip3
    val nbase = base.count(b => b)
    val nrecs = recs.count(b => b)

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
}

package cuvee.lemmas.recognize

import cuvee.pure._
import cuvee.lemmas._

import cuvee.util.Name
import scala.collection.mutable.ListBuffer

object Conditional {
  // Entrypoint to check every Parameter of df for conditional Identity behavior over df
  // Returns for every Parameter `i` a Lemma and a Precondition, so that the Function behaves like a identity Function over `i`
  def checkConditionalIdentityForEveryParameter(df: Def): List[(Rule, Def)] = {
    var Def(f, cases) = df
    var Fun(name, _, args, res) = f

    val results =
      for (
        (arg, n) <- args.zipWithIndex if arg == res;
        res <- checkCasesForCondIdentAtIndex(cases, n, f)
      )
        yield res

    return results
  }

  // Checks the conditional Identity behavior for a given Parameter index iterating through every case, calling checkCaseForCondIdentAtIndex
  // Returns a Lemma and the precondition, if the precondition contains at least one recursive and base case showing identity behavior of df (not FALSE precondition case body)
  def checkCasesForCondIdentAtIndex(
      cases: List[C],
      pos: Int,
      recfunc: Fun
  ): Option[(Rule, Def)] = {
    var Fun(recfuncname, recfuncparams, recfuncargs, recfuncret) = recfunc
    // Precondition Function Declaration
    var prefun = Fun(Name(recfuncname + "_id?", Some(pos)), recfuncparams, recfuncargs, Sort.bool)

    var countBaseRecCasesAndGenPreCases =
      for (c @ C(caseargs, caseguard, casebody) <- cases)
        yield checkCaseForCondIdentAtIndex(c, pos, recfunc) match {
          case None =>
            (0, 0, C(caseargs, caseguard, False))

          case Some((Nil,prebody)) => 
            (1,0,C(caseargs, caseguard, prebody))

          case Some((recarglists,prebody)) =>
            val recs = recarglists map (App(prefun, _))
            val rec = if (c.isRecursive(recfunc)) 1 else 0
            (1 - rec, rec, C(caseargs, caseguard, And(recs)))
        }
    
    val (base, recs, precases) = countBaseRecCasesAndGenPreCases.unzip3
    val nbase = base.sum
    val nrecs = recs.sum

    if (nbase > 0 && nrecs > 0) {
      val xs = Expr.vars("x", recfuncargs)
      val cond = App(prefun, xs)
      val lhs = App(recfunc, xs)
      val rhs = xs(pos)
      // Lemma and Precondition Generation
      val eq = Rule(lhs, rhs, cond)
      val defpre = Def(prefun, precases.toList)
      Some((eq, defpre))
    } else {
      None
    }
  }

  // Infers a preconditions case, so that the given case of df is Ident over a given Parameter.
  // Returns recursive Arguments or a base case of the precondition.
  def checkCaseForCondIdentAtIndex(c: C, pos: Int, recfunc: Fun): Option[(List[List[Expr]], Expr)] = {
    val C(args, guard, body) = c
    val argPick = args(pos)

    (argPick,body) match {
      // Base cases
      case (arg: Var,body) if arg == body =>
        Some(Nil, True)
      
      case (arg: Lit,body) if arg == body =>
        Some(Nil, True)

      case (arg: Var, body) if !c.isRecursive(recfunc) =>
        Some(Nil, arg === body)
      
      case (arg: Lit, body) if !c.isRecursive(recfunc) =>
        Some(Nil, arg === body)

      // Recursive Case
      case (App(f, pAppParamList),body) =>
        body match {
          //Constructors of Parameter and Body have to match
          case App(g, bAppParamList) if f == g => {
            //Each argument has to match
            val stuff = (pAppParamList zip bAppParamList) map {
              case (pAppParam: Var, bAppParam) if pAppParam == bAppParam =>
                true -> None
              case (pAppParam: Lit, bAppParam) if pAppParam == bAppParam =>
                true -> None
              //Recurisve Call: The Arguemnt of the Recursive Call at Position pos, 
              //                needs to be the same to the current argument of the Parameters Constructor
              case (pAppParam: Var, App(Inst(`recfunc`, _), recargs))
                  if pAppParam == recargs(pos) =>
                true -> Some(recargs)
              case (pAppParam: Lit, App(Inst(`recfunc`, _), recargs))
                  if pAppParam == recargs(pos) =>
                true -> Some(recargs)
              case (pAppParam: App, App(Inst(`recfunc`, _), recargs))
                  if pAppParam == recargs(pos) =>
                true -> Some(recargs)
              case other =>
                false -> None
            }

            val (oks, recargs) = stuff.unzip
            if (oks forall (b => b)) {
              Some(recargs.flatten, True) //True is a spaceholder, the body will be the recursive call of pre
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

  // Entrypoint to check a Functiondefinition df to be conditional recursion free or constant
  // Returns one Lemma with Precondition describing df beeing conditional recursion free
  def checkIsDefConstant(df: Def): Option[(Rule, Def)] = {
    var Def(f, cases) = df
    checkCasesAsConstant(cases, f, df.staticArgs)
  }

  // Iterates through every case of df calling checkCaseAsConstant, constructing the precondition. 
  // Returns Lemma with precondition, if pre contains at least one base and recursive case (no FALSE body)
  def checkCasesAsConstant(
      cases: List[C],
      recfunc: Fun,
      static: List[Int]
  ): Option[(Rule, Def)] = {
    var Fun(recfuncname, recfuncparams, recfuncargs, recfuncret) = recfunc
    // Precondition Function Declaration
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
          // Lemma and Precondition Generation
          val eq = Rule(lhs, rhs, cond)
          val defpre = Def(prefun, precases)
          Some((eq, defpre))
        } else {
          None
        }
      case other => None
    }
  }

  // Checks given case for constant behavior
  // returns the recursive arguments for pre, or the constant part of the function
  def checkCaseAsConstant(
      c: C,
      recfunc: Fun,
      static: List[Int],
      recargsToStatic: List[Var]
  ): (Option[List[Expr]], Option[Expr]) = {

    val isConstantRecArgsConstPart = c match {
      // recursive cases are only tail recursive
      case c @ C(args, guard, App(Inst(`recfunc`, _), recargs)) =>
        true -> (Some(recargs), None)
      // a base case is constant, if the free Variables of the bodys case 
      // appear in the free and static (arguments staying same accross every recursive call)) case Parameters
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

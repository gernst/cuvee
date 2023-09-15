package cuvee.lemmas

import cuvee.util.Name
import cuvee.pure._

object Unused {
  // removes unused parameters, returning:
  // - a flag whether the definition was changed
  // - the old or new definition if changed
  // - the updated argument lists
  // if rename is not none, then the new function will have that name,
  // otherwise, the old name is kept; this is used if an original function must be kept
  def unused(df: Def, xs: List[Expr], rename: Option[Name] = None): (Boolean, Def, List[Expr]) = {
    val Def(f, cases) = df

    val is = usedArgs(df)

    val name_ = rename getOrElse f.name
    val args_ = is map f.args
    val params_ = f.params filter (_ in args_)
    val f_ = Fun(name_, params_, args_, f.res)

    val cases_ = for (C(args, guard, body) <- cases) yield {
      C(is map args, guard, keep(f, f_, is, body))
    }

    val df_ = Def(f_, cases_)
    (f_.arity < f.arity, df_, is map xs)
  }

  def keep(f: Fun, f_ : Fun, is: List[Int], e: Expr): Expr = e match {
    case k: Lit => k
    case y: Var => y

    case App(Inst(`f`, su), args) =>
      // get rid of superflous parameters here
      val su_ = su filter { case (p, t) => f_.params contains p }
      App(Inst(f_, su_), is map args)

    case App(inst, args) =>
      App(inst, args map (keep(f, f_, is, _)))
  }

  // compute those argument positions that are needed
  def usedArgs(df: Def): List[Int] = {
    val (xs, ys) = usedAndUnusedArgs(df)
    xs
  }

  def usedAndUnusedArgs(df: Def): (List[Int], List[Int]) = {
    val Def(f, cases) = df
    val is = 0 until f.args.length
    is.toList.partition { i: Int =>
      cases exists { case C(args, guard, body) =>
        args(i) match {
          case x: Var =>
            (x in guard) || isUsed(f, i, x, body)
          case _ =>
            true
        }
      }
    }
  }

  def isUsed(f: Fun, i: Int, x: Var, e: Expr): Boolean = e match {
    case _: Lit => false
    case y: Var => x == y

    case App(Inst(`f`, _), args) =>
      args.zipWithIndex.exists { case (arg, j) =>
        j != i && isUsed(f, i, x, arg)
      }

    case App(_, args) =>
      args.exists(isUsed(f, i, x, _))
  }
}

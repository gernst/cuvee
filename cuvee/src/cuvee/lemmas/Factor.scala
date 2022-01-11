package cuvee.lemmas

import cuvee.util.Map_
import cuvee.pure._
import cuvee.StringOps

object Factor {
  // Lift base cases out of a given definition,
  // where ks are the indices of the cases of df that
  // depend on constants or constantly propagated arguments only (cf. Util.constantResults)
  def base(df: Def[Norm], ks: List[Int]): (Def[Norm], List[Def[Norm]], Rule) = {
    val Def(f, cases) = df

    // a list of fresh variables, one for each original argument of f
    val xs = Util.vars("x", f.args)

    // additional variables, one for each base case of the definition,
    // unless that base case is given by  variable already which is passed down unmodified
    val zs_ =
      for ((c, k) <- cases.zipWithIndex)
        yield
          if (c.isBaseCase && !(c.d.isInstanceOf[Var] && (ks contains k)))
            Some(Var("z", f.res, Some(k)))
          else
            None

    // while zs_ contains an entry for *all* cases and can therefore be indexed accordingly,
    // zs collects only those entries which are not None, i.e., can be factored out
    val zs = zs_.flatten

    // function f' receives the original arguments and one additional argument per base case
    // that can be factored out
    val f_ = Fun(f.name + "'", f.params, f.args ++ zs.types, f.res)

    // transform each case, returning optionally
    // - an expression that denotes the respective base case value
    // - a definition of a function that computes base cases that are not constant
    val stuff =
      for ((Norm(args, guard, as, bs, cs, d), k) <- cases.zipWithIndex)
        yield (bs, zs_(k)) match {
          // simple case: we can factor the base case value d via the argument given by zk
          case (Map_(), Some(zk)) if ks contains k =>
            // the base case is expressed over variables in the pattern
            // but we need it for the common set of variables xs that are used in the equivalence below,
            // this renaming performs the mapping, it is ok, because we know that
            // since d depends on constant arguments only, its free variables must occur
            // top-level in the argument list of that case and not inside a nested constructor pattern
            val re =
              Expr.subst(
                for ((a: Var, x) <- args zip xs)
                  yield (a, x)
              )

            val res = Norm(args ++ zs, guard, as, Map(), cs, zk)
            val arg = Some(d rename re)
            val dfs = None
            (res, arg, dfs)

          // this case works similarly but we need to introduce a recursive function
          // that mirrors the changes to the arguments/free variables used in d
          case (Map_(), Some(zk)) =>
            val re =
              Expr.subst(
                for ((a: Var, x) <- args zip xs)
                  yield (a, x)
              )

            // keep recursive cases + the single base case we are currently looking at,
            // we ignore all other base cases, they won't matter.
            // this works for linear recursions only, such that the number
            // of extra functions is constant (i.e., no tree structure needs to be generated),
            // and we can map then one-to-one on the respective base cases
            val cases_ =
              for (
                (Norm(args, guard, as, bs, cs, _), j) <-
                  cases.zipWithIndex if j == k || bs.nonEmpty
              )
                yield bs match {
                  case Map_() =>
                    Norm(args, guard, as, bs, Map(), d)
                  case Map_((y, b)) => // works only for linear recursion!
                    Norm(args, guard, as, bs, Map(), y)
                }

            val g = f copy (name = (f.name + "_base") __ k)

            val res = Norm(args ++ zs, guard, as, Map(), cs, zk)
            val arg = Some(App(g, xs))
            val dfs = Some(Def(g, cases_))
            (res, arg, dfs)

          case _ =>
            // we just have to pass down the arguments that capture
            // the factored values in recursive calls
            val bs_ =
              for ((y, b) <- bs)
                yield (y, b ++ zs)

            val res = Norm(args ++ zs, guard, as, bs_, cs, d)
            val arg = None
            val dfs = None
            (res, arg, dfs)
        }

    val (cases_, as_, dfs_) = stuff.unzip3
    val as = as_.flatten

    val df_ = Def(f_, cases_)

    // remove unused arguments from df_
    val us = Util.usedArgs(df_)
    val cases__ =
      for (Norm(args, guard, as, bs, cs, d) <- cases_)
        yield {
          val bs_ =
            for ((y, b) <- bs)
              yield (y, us map b)
          Norm(us map args, guard, as, bs_, cs, d)
        }
    val f__ = f_ copy (args = us map f_.args)
    val df__ = Def(f__, cases__)

    val eq = Rule(App(f, xs), App(f__, us map (xs ++ as)), True)

    (df__, dfs_.flatten, eq)
  }

  // factor arguments that are computed with a variables before passing them down the recursion
  // TODO: do not do this for purely tail-recursive functions
  def arguments(df: Def[Norm], kc: List[Int]): List[Def[Norm]] = {
    val Def(f, cases) = df
    val params = f.params
    val types = f.args

    val k = types.length

    val fs =
      for ((res, i) <- types.zipWithIndex if kc contains i)
        yield Fun(f.name + "_arg" __ i, params, types, Sort.list(res))

    fs map println
    println()
    
    Nil
    // val cases_ =
    //   for (Norm(xs, args, guard, as, bs, cs, d) <- cases)
    //     yield bs match {
    //       case Nil =>
    //         for (_ <- fs)
    //           yield {
    //             val d = Fun.nil()
    //             Norm(xs, args, guard, as, Nil, Nil, d)
    //           }

    //       case List((y, args_)) =>
    //         require(
    //           fs.length == as.length,
    //           "invalid number of a-variables, expected " + fs.length + ", but have " + as
    //         )

    //         for ((fa, (x, a)) <- fs zip as)
    //           yield {
    //             val y_ = Var(y.name, fa.res, y.index)
    //             val d = x :: y_
    //             Norm(xs, args, guard, as, List(y_ -> args_), Nil, d)
    //           }
    //     }

    // for ((f, cs) <- fs zip cases_.transpose)
    //   yield Def(f, cs)
  }
}

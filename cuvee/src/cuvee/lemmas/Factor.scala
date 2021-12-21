package cuvee.lemmas

import cuvee.pure._

object Factor {
  def base(df: Def, ks: List[Int]): (Def, List[Def], Rule) = {
    val Def(f, cases) = df

    val xs = Util.vars("x", f.args)

    val zs_ =
      for ((c, k) <- cases.zipWithIndex)
        yield
          if (c.isBaseCase)
            Some(Var("z", f.res, Some(k)))
          else
            None

    val zs = zs_.flatten

    val f_ = Fun(f.name + "'", f.params, f.args ++ zs.types, f.res)
    val stuff =
      for (
        (Case(ys, args, guard, Norm(as, bs, cs, d)), k) <- cases.zipWithIndex
      )
        yield (bs, zs_(k)) match {
          case (Nil, Some(zk)) if ks contains k =>
            val re =
              Expr.subst(
                for ((a: Var, x) <- args zip xs)
                  yield (a, x)
              )

            val res = Case(ys, args ++ zs, guard, Norm(as, Nil, cs, zk))
            val arg = Some(d rename re)
            val dfs = None
            (res, arg, dfs)

          case (Nil, Some(zk)) =>
            val re =
              Expr.subst(
                for ((a: Var, x) <- args zip xs)
                  yield (a, x)
              )

            // keep recursive cases + that one base case
            val cases_ =
              for (
                (Case(_, args, guard, Norm(as, bs, cs, _)), j) <-
                  cases.zipWithIndex if j == k || bs.nonEmpty
              )
                yield {
                  Case(xs, args, guard, Norm(as, bs, Nil, d))
                }

            import cuvee.StringOps
            val g = f copy (name = (f.name + "_base") __ k)

            val res = Case(ys, args ++ zs, guard, Norm(as, Nil, cs, zk))
            val arg = Some(App(g, xs))
            val dfs = Some(Def(g, cases_))
            (res, arg, dfs)

          case _ =>
            val bs_ =
              for ((y, b) <- bs)
                yield (y, b ++ zs)

            val res = Case(ys, args ++ zs, guard, Norm(as, bs_, cs, d))
            val arg = None
            val dfs = None
            (res, arg, dfs)
        }

    val (cases_, as_, dfs_) = stuff.unzip3
    val as = as_.flatten

    val df_ = Def(f_, cases_)
    val eq = Rule(xs, App(f, xs), App(f_, xs ++ as), True)

    (df_, dfs_.flatten, eq)
  }

  //

  // val ds =
  //   for (
  //     (Case(_, args, guard, Norm(as, Nil, cs, d)), k) <- cases.zipWithIndex
  //   )
  //     yield {
  //       if (ks contains k) {
  //         // need to adjust free variables in d
  //         val re =
  //           Expr.subst(
  //             for ((a: Var, x) <- args zip xs)
  //               yield (a, x)
  //           )
  //         (d rename re, None)
  //       } else {
  //         val cases_ =
  //           for (
  //             (Case(_, args, guard, Norm(as, bs, cs, _)), j) <-
  //               cases.zipWithIndex if j == k || bs.nonEmpty
  //           )
  //             yield {
  //               Case(xs, args, guard, Norm(as, bs, Nil, d))
  //             }

  //         import cuvee.StringOps
  //         val g = f copy (name = (f.name + "_base") __ k)

  //         (App(g, xs), Some(Def(g, cases_)))
  //       }
  //     }

  // val (ys, dfa) = ds.unzip
  // val df_ = Def(f_, cases_)
  // val eq = Rule(xs, App(f, xs), App(f_, xs ++ ys), True)

  // (df_, dfa.flatten, eq)
}

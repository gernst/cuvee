package cuvee.lemmas

import cuvee.pure._

object Util {
  def liftIte(
      fun: Fun,
      inst: Inst,
      rdone: List[Expr],
      todo: List[Expr]
  ): Expr = {
    todo match {
      case Nil =>
        App(fun, inst, rdone.reverse)
      case Ite(test, left, right) :: rest =>
        val _left = liftIte(fun, inst, rdone, left :: rest)
        val _right = liftIte(fun, inst, rdone, right :: rest)
        Ite(test, _left, _right)
      case arg :: rest =>
        liftIte(fun, inst, arg :: rdone, rest)
    }
  }

  def liftIte(expr: Expr): Expr = {
    expr match {
      case App(fun, inst, args) =>
        liftIte(fun, inst, Nil, args)
      case _ =>
        expr
    }
  }

  def vars(name: String, types: List[Type]) = {
    for ((t, i) <- types.zipWithIndex)
      yield Var("x", t, Some(i))
  }

  def simplify(df: Def): Option[(Def, Rule)] = {
    ???
  }

  // compute those argument positions that are needed
  def usedArgs(df: Def): List[Int] = {
    val ks = cuvee.fix(used(df, _))
    ks.toList.sorted
  }

  // compute those argument positions that are propagated constantly
  def constantArgs(df: Def): List[Int] = {
    val Def(f, cases) = df
    val n = f.args.length

    val all = List.tabulate(n)((i: Int) => i)

    all.filter { case i =>
      cases forall { case Case(args, guard, as, bs, cs, d) =>
        bs forall { case (x, recs) =>
          recs(i) == args(i)
        }
      }
    }
  }

  // compute those argument positions that are not propagated constantly,
  // and that in addition require some computation ("a" variable present)
  // Note:
  // * no purely tail-recursive functions
  // * only linear recursion (otherwise cannot use a list to represent args)
  def computedArgs(df: Def): List[Int] = {
    val Def(f, cases) = df
    val n = f.args.length

    val all = List.tabulate(n)((i: Int) => i)

    val linear = cases forall { case Case(args, guard, as, bs, cs, d) =>
      bs.size <= 1
    }

    val tailrec = cases forall { case Case(args, guard, as, bs, cs, d) =>
      bs.isEmpty || (bs exists { case (x, recs) => x == d })
    }

    all.filter { case i =>
      val computed = cases exists { case Case(args, guard, as, bs, cs, d) =>
        bs exists { case (x, recs) =>
          as exists (_._1 == recs(i))
        }
      }

      linear && computed // && !tailrec
    }
  }

  // compute results that are constant or only depend on constant arguments
  // but which are not just variables already
  def constantResults(df: Def, ks: List[Int]): List[Int] = {
    val Def(f, cases) = df

    val zs =
      for ((Case(args, guard, as, bs, cs, d), i) <- cases.zipWithIndex)
        yield d match {
          // case x: Var =>
          //   (i, false)
          case _ =>
            val ka = ks map args
            (i, d.free subsetOf ka.free)
        }

    zs collect { case (i, true) => i }
  }

  def used(df: Def, is: Set[Int]): Set[Int] = {
    val Def(f, cases) = df

    val ks =
      for (Case(args, guard, as, bs, cs, d) <- cases)
        yield {
          val zs = d.free

          // cs vars needed for d
          val ys =
            for (
              (x, c) <- cs if zs contains x;
              y <- c.free
            )
              yield y

          // bs vars needed for d, but only for parameters that are known to matter
          val ws =
            for (
              (x, args) <- bs if zs contains x;
              (e, i) <- args.zipWithIndex if is contains i;
              y <- e.free
            )
              yield y

          // as vars needed for bs/cs or the guard
          val vs_ =
            for (
              (x, a) <- as if (ws.toList contains x) || (zs contains x);
              y <- a.free
            )
              yield y

          val vs = guard.free ++ zs ++ ys ++ ws ++ vs_

          for (
            (arg, k) <-
              args.zipWithIndex // note: pattern matching counts as use
            if (!arg.isInstanceOf[Var]) || (arg.free intersects vs)
          )
            yield k
        }

    ks.flatten.toSet
  }
}

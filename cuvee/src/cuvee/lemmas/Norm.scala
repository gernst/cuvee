package cuvee.lemmas

import cuvee.pure._
import cuvee.StringOps

case class Norm(
)

case class Case(
    xs: List[Var],
    args: List[Expr],
    guard: List[Expr],
    as: List[(Var, Expr)],
    bs: List[(Var, List[Expr])],
    cs: List[(Var, Expr)],
    d: Expr
) {
  def isBaseCase = bs.isEmpty
}

object Norm {
  def lift(df: Def, dfs_a: List[Def], st: State): (Def, Rule) = {
    val nil = st funs "nil"
    val cons = st funs "cons"
    val Def(f, cases) = df

    val at = dfs_a map (_.fun.res)
    val f_ = Fun(f.name + "'", f.params, f.args ++ at, f.res)

    val cases_ =
      for (Case(xs, args, guard, as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            val as_ =
              for (_ <- dfs_a)
                yield App(nil, Nil)
            Case(xs, args ++ as_, guard, Nil, Nil, cs, d)

          case List((y, es)) =>
            val ar_as_ =
              for ((a, _) <- as)
                yield {
                  val ar = Var(a.name + "s", Sort.list(a.typ), a.index)
                  ar -> App(cons, List(a, ar))
                }
            val (ar, as_) = ar_as_.unzip
            val bs_ = List((y, es ++ ar))
            Case(xs, args ++ as_, guard, Nil, bs_, cs, d)
        }

    val df_ = Def(f_, cases_)

    val xs =
      for ((t, i) <- df.fun.args.zipWithIndex)
        yield Var("x", t, Some(i))

    val as =
      for (df_a <- dfs_a)
        yield App(df_a.fun, xs)

    val lhs = App(df.fun, xs)
    val rhs = App(df_.fun, xs ++ as)
    val eq_ = Rule(xs, lhs, rhs, True)

    (df_, eq_)
  }

  def lift(df: Def, df_cr: Def, df_cb: Def, st: State): (Def, Rule) = {
    val nil = st funs "nil"
    val cons = st funs "cons"
    val Def(f, cases) = df

    val fr = df_cr.fun
    val fb = df_cb.fun
    val f_ = Fun(f.name + "'", f.params, List(fr.res, fb.res), f.res)

    val Sort(Con.list, List(typ)) = fr.res

    var j = 0
    var k = 0

    val cases_ =
      for (Case(zs, args, guard, as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            val ar = App(nil, Nil)
            val ab = Expr.in(j, d, fb.res)
            j += 1
            Case(zs, List(ar, ab), guard, Nil, Nil, Nil, d)

          case List((y, es)) =>
            // println(fb)
            // println(fr)
            val x = Expr.in(k, Expr.tuple(cs map (_._1)), typ)
            val xs = Var(y.name + "s", fr.res, y.index)
            // println(x + ": " + x.typ)
            // println(xs.toStringTyped)
            val ar = App(cons, List(x, xs))
            val ab = Var("cb", fb.res)
            k += 1
            Case(zs, List(ar, ab), guard, Nil, List(y -> List(xs, ab)), Nil, d)
        }

    val df_ = Def(f_, cases_)

    val xs =
      for ((t, i) <- f.args.zipWithIndex)
        yield Var("x", t, Some(i))

    val lhs = App(f, xs)
    val rhs = App(f_, List(App(fr, xs), App(fb, xs)))
    val eq_ = Rule(xs, lhs, rhs, True)

    (df_, eq_)
  }

  def map(df: Def, st: State): Def = {
    val nil = st funs "nil"
    val cons = st funs "cons"

    val Def(f, cases) = df

    // fails if there are no recursive cases
    // e.g. for fused functions where the recursive call was not contracted
    val types =
      for (Case(xs, args, guard, as, bs, cs, d) <- cases if bs.nonEmpty)
        yield Sort.prod(cs map (_._1.typ))
    val res = Sort.sum(types)

    val f_ = Fun(f.name + "_cr", f.params, f.args, Sort.list(res))

    var k = 0

    val cases_ =
      for (Case(zs, args, guard, as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            val d = App(nil, Nil)
            Case(zs, args, guard, as, Nil, Nil, d)

          case List((x, es)) =>
            val xs = Var(x.name + "s", f_.res, x.index)

            val y = Expr.fresh("c", res)
            val c = Expr.in(k, Expr.tuple(cs map (_._2)), res)
            k += 1 // count only recursive cases

            val d = App(cons, List(y, xs))
            Case(zs, args, guard, as, List(xs -> es), List(y -> c), d)
        }

    Def(f_, cases_)
  }

  def base(df: Def, st: State): Def = {
    val Def(f, cases) = df

    val types =
      for (Case(xs, args, guard, as, bs, cs, d) <- cases if bs.isEmpty)
        yield d.typ
    val res = Sort.sum(types)

    val f_ = Fun(f.name + "_cb", f.params, f.args, res)

    var k = 0

    val cases_ =
      for (Case(zs, args, guard, as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            val d_ = Expr.in(k, d, res)
            k += 1 // count only base cases
            Case(zs, args, guard, as, Nil, cs, d_)

          case List((x, es)) =>
            Case(zs, args, guard, as, List(x -> es), Nil, x)
        }

    Def(f_, cases_)
  }

  def rec(df: Def, st: State): Def = {
    val nil = st funs "nil"
    val cons = st funs "cons"

    val Def(f, cases) = df

    val f_ = Fun(f.name + "_b", f.params, f.args, Sort.list(f.res))

    val cases_ =
      for (Case(zs, args, guard, as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            val d = App(nil, Nil)
            Case(zs, args, guard, as, Nil, Nil, d)

          case List((x, es)) =>
            val xs = Var(x.name + "s", f_.res, x.index)
            val d = App(cons, List(x, xs))
            Case(zs, args, guard, as, List(xs -> es), Nil, d)
        }

    Def(f_, cases_)
  }

  def ana(df: Def, st: State): List[Def] = {
    val nil = st funs "nil"
    val cons = st funs "cons"

    val Def(f, cases) = df
    val params = f.params
    val types = f.args

    val k = types.length

    val fs =
      for ((res, i) <- types.zipWithIndex)
        yield Fun(f.name + "_a" __ i, params, types, Sort.list(res))

    val cases_ =
      for (Case(xs, args, guard,as, bs, cs, d) <- cases)
        yield bs match {
          case Nil =>
            for (_ <- fs)
              yield {
                val d = App(nil, Nil)
                Case(xs, args, guard, as, Nil, Nil, d)
              }

          case List((y, args_)) =>
            require(
              fs.length == as.length,
              "invalid number of a-variables, expected " + fs.length + ", but have " + as
            )

            for ((fa, (x, a)) <- fs zip as)
              yield {
                val y_ = Var(y.name, fa.res, y.index)
                val d = App(cons, List(x, y_))
                Case(xs, args, guard, as, List(y_ -> args_), Nil, d)
              }
        }

    for ((f, cs) <- fs zip cases_.transpose)
      yield Def(f, cs)
  }
}

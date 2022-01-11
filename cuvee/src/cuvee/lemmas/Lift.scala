package cuvee.lemmas

import cuvee.pure._

case class Lift(
    y: List[Var],
    z: Var,
    f: Expr,
    b: Expr,
    g: Expr
) {
  // def neutral = {
  //   val su = Map(y -> b)
  //   Eq(g subst su, y)
  // }

  // def commute = {
  //   val su1 = Map(y -> g)
  //   val su2 = Map(y -> f)
  //   Eq(f subst su1, g subst su2)
  // }
}

object Lift {
  def apply(
      y: Var,
      z: Var,
      f: Expr,
      b: Expr,
      g: Expr
  ): Lift =
    Lift(List(y), z, f, b, g)

  val m = Var("m", Sort.int)
  val n = Var("n", Sort.int)
  val k = Var("k", Sort.int)

  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)
  val r = Var("r", Sort.bool)

  val x = Var("x", Fun.a)
  val y = Var("y", Fun.b)
  val z = Var("z", Fun.a)
  val xs = Var("xs", Fun.list)
  val ys = Var("ys", Fun.list)
  val zs = Var("zs", Fun.list)
  val nil = App(Fun.nil, Nil)

  val A = Sort(Con("A", 0), Nil)
  val B = Sort(Con("B", 0), Nil)
  val b = Var("b", B)
  val f = Fun("f", Nil, List(A, B), B)
  val g = Fun("g", Nil, List(B, B), B)

  val lifts = List(
    // Lift(List(x, y), y, z, f(x, y), b, g(y, z)),
    Lift(m, k, n + m, Zero, m + k),
    Lift(m, k, m + n, Zero, k + m),
    Lift(m, k, n * m, One, m * k),
    Lift(m, k, m * n, One, k * m),
    Lift(p, r, q or p, False, p or r),
    Lift(p, r, p or q, False, r or p),
    Lift(p, r, q and p, True, p and r),
    Lift(p, r, p and q, True, r and p),
    Lift(ys, zs, x :: ys, nil, ys ++ zs),
    Lift(ys, zs, ys ++ xs, nil, zs ++ ys),
    Lift(ys, zs, xs ++ ys, nil, ys ++ zs)
  )

  def main(args: Array[String]) {
    // for (lift <- lifts) {
    //   println(lift.neutral)
    //   println(lift.commute)
    // }
  }

//   def assumptions(f: Fun, z: Expr, g: Fun): List[Rule] = {
//     Nil
//   }

//   def assumptions(): List[Rule] = {
//     val rs =
//       for (
//         (f, (z, g)) <- commute;
//         phi <- assumptions(f, z, g)
//       )
//         yield phi

//     rs.toList
//   }

  def lift(df: Def) = {
    val Def(h, cases) = df
    // println("0. " + h.name)

    for (l @ Lift(ys, z, f, b, g) <- lifts) {
      val ok =
        for (Case(args, guard, as, bs, cs, d) <- cases if bs.nonEmpty)
          yield Rewrite.bind(f, d) match {
            case None =>
              // println("1. " + h.name + " failed")
              (false, bs.exists (_._1 == d)) // direct pass onwards
            case Some(env) =>
              // println("1. " + h.name + " " + ys + " " + env)
              (ys forall { y =>
                bs exists (_._1 == env(y)) // y must denote a recursive call
              }, true)
          }

      val (yes, maybe) = ok.unzip

      if (yes.exists(b => b) && maybe.forall(b => b)) {
        // println("2. " + h.name + " with " + l)
        val pos =
          for (Case(args, guard, as, bs, cs, d) <- cases if bs.isEmpty)
            yield args indexOf d

        if (pos forall (_ >= 0)) {
          // println("3. " + h.name)
          val xs =
            for ((t, i) <- h.args.zipWithIndex)
              yield Var("x", t, if (pos contains i) None else Some(i))
          // this case distinction collapses all base cases to the *same* variable
          // which is needed because commutation cannot discern different base cases
          // (we do not know which one is triggered)

          val as =
            for ((x, i) <- xs.zipWithIndex)
              yield if (pos contains i) b else x
          val bs =
            for ((x, i) <- xs.zipWithIndex if pos contains i)
              yield x

          val lhs = App(h, xs)
          val arg = App(h, as)

          val su1 = bs map (z -> _)
          val su2 = ys map (_ -> arg)
          val su = Expr.subst(su1 ++ su2)
          // println("4. " + h.name + " " + su)
          val rhs = g subst su

          val vs = xs collect { case v: Var => v }
          println(Forall(vs.distinct, Eq(lhs, rhs)))
          println()
        }
      }
    }
  }
}

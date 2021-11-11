package cuvee.pure

object Test {
  val a = Univ.param("a")

  val univ = Univ(
    "Bool" -> Univ.con("Bool", 0),
    "Int" -> Univ.con("Int", 0),
    "List" -> Univ.con("List", 1)
  )

  val bool = univ.sort("Bool", List())
  val list_a = univ.sort("List", List(a))
  val int = univ.sort("Int", List())
  val list_int = univ.sort("List", List(int))
  val list_bool = univ.sort("List", List(bool))

  val eqn = Sig.fun("=", List(a), List(a, a), bool)
  val nil = Sig.fun("nil", List(a), List(), list_a)
  val cons = Sig.fun("cons", List(a), List(a, list_a), list_a)

  val sig = Sig(
    "=" -> eqn,
    "nil" -> nil,
    "cons" -> cons
  )

  def main(args: Array[String]) {
    println(univ)
    println(sig)

    val exprs = new sig.Exprs

    val n = exprs.lit(0, int)
    val b = exprs.lit(false, bool)
    val xs = exprs.x("xs", list_int)
    val ys = exprs.x("ys", list_bool)
    val zs = exprs.x("zs", list_a)

    val nil = exprs.const("nil")
    val expr1 = exprs.app("=", List(xs, exprs.app("cons", List(n, zs))))
    val expr2 = exprs.app("=", List(nil, exprs.app("cons", List(b, zs))))

    println(expr1.resolve)
    println(expr2.resolve)
  }
}

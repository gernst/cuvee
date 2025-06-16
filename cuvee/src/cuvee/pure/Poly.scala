package cuvee.pure

/* Represents a variable or function in Poly.
 * For a variable the args list is empty.
 */
case class Mono(k: BigInt, e: Expr) {
  def unary_-() =
    Mono(-k, e)

  def *(c: BigInt) =
    Mono(k * c, e)

  def *(that: Mono) =
    Mono(this.k * that.k, this.e * that.e)

  // def /(d: BigInt) = { assert(k % d == 0) Mono(k / d, x) }
  def /(d: BigInt): Option[Mono] =
    if (k % d != 0)
      None
    else
      Some(Mono(k / d, e))

  override def toString = k + "*" + e
  def isZero = (k == 0)

  def toExpr = {
    if (k == 0) Lit(k, Sort.int)
    else if (k == 1) e
    else if (k == -1) -e
    else Lit(k, Sort.int) * e
  }
}

/* The idea is to flatten the original structure and then restructure it into:
 * a + xb + yc + .... with Plus(args) and args being Exprs that are a, xb, yc
 * The Exprs a, xb ... are of the structure Times(args)
 * so basicly b * x with b as Num and x as an Expr (for example just a variable or an function)
 */
case class Poly(c: BigInt, ms: List[Mono]) {
  def unary_-() =
    Poly(-c, ms map (-_))

  def +(that: Poly) =
    Poly(this.c + that.c, this.ms ++ that.ms)

  def -(that: Poly) =
    this + (-that)

  def *(that: Poly): Poly = {
    val c = this.c * that.c
    val cs1 = this.ms map (_ * that.c)
    val cs2 = that.ms map (_ * this.c)
    val ms = for (m1 <- this.ms; m2 <- that.ms) yield m1 * m2
    Poly(c, cs1 ++ cs2 ++ ms)
  }

  def compact: Poly = {
    val groups = ms groupBy (_.e)

    val ms_ =
      for ((e, ms) <- groups)
        yield Mono(ms.map(_.k).sum, e)

    Poly(c, ms_.toList filterNot (mono => mono.k == 0))
  }

  /* Returns a list of all possible Ids to solve
   * You could of course just use a fun, but thats harder and i dont want to right now
   */
  def vars(): List[Var] =
    ms collect { case Mono(k, x: Var) => x }

  /*
   * Try to solve for the entered Id.
   */
//   def solve(id: Id): Option[Poly] = {
//     ms.partition(_.x == id) match {
//       case (List(Mono(k, _, _)), bs) =>
//         cuvee.ensure(k != 0, "non-compacted polynomial", this)

//         val cs = bs map (x => (-x / k).getOrElse(return None))
//         if (c % k == 0)
//           Some(Poly(-c / k, cs))
//         else
//           None

//       case (Nil, _) =>
//         None

//       case _ =>
//         cuvee.error("non-compacted polynomial", this)
//     }
//   }

  override def toString = {
    if (ms.isEmpty) c.toString
    else if (c == 0) ms.mkString(" + ")
    else (c :: ms).mkString(" + ")
  }

  def toExpr = {
    if (ms.isEmpty) Lit(c, Sort.int)
    else if (c == 0) Plus(ms map (_.toExpr))
    else Plus(Lit(c, Sort.int) :: (ms map (_.toExpr)))
  }
}

object Poly {
  val empty = const(0)
  def const(c: BigInt) = Poly(c, Nil)
  def factor(k: BigInt, e: Expr) = Poly(0, List(Mono(k, e)))

  def simplify(expr: Expr) = {
    val poly = apply(expr)
    poly.compact.toExpr
  }

  /*
   * Try to build a linear polynomial form out of an Expr */
  def apply(expr: Expr): Poly = {
    expr match {
      case Lit(value: BigInt, Sort.int) =>
        Poly.const(value)

      case UMinus(arg) =>
        val flat = apply(arg)
        -flat

      case Plus(args) =>
        val flat = args map apply
        flat reduce (_ + _)

      case Times(args) =>
        val flat = args map apply
        flat reduce (_ * _)

      case Minus(arg1, arg2) =>
        val flat1 = apply(arg1)
        val flat2 = apply(arg2)
        flat1 - flat2

      case _ =>
        Poly.factor(1, expr)
    }
  }
}

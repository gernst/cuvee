package cuvee.imp.annotate

import cuvee.SetOps
import cuvee.pure._
import cuvee.imp.Path

case class Counter(init: Expr, step: BigInt)

object Accelerate {
  val plus_one = BigInt(1)
  val minus_one = BigInt(-1)

  def isEarlierValueOf(
      counter: Counter,
      current: Var,
      rho: Map[Var, Var]
  ): Option[Expr] = {
    counter match {
      case Counter(init, `plus_one`) =>
        Some(init <= rho(current) && rho(current) < current)

      case Counter(init, `minus_one`) =>
        Some(current < rho(current) && rho(current) <= init)

      case _ =>
        None
    }
  }

  def lbsFromCounter(counters: Map[Var, Counter]): List[Expr] = {
    val lb = for ((var_, counter) <- counters) yield {
      counter match {
        case Counter(init, `plus_one`) =>
          init <= var_

        case Counter(init, `minus_one`) =>
          var_ <= init

        case _ =>
          True
      }
    }
    lb.toList
  }

  def ubAndDecreaseFromTest(test: List[Expr]): (Expr, Expr) = test match {
    case Lt(left, right) :: next =>
      val ub = left <= right
      val decreases = right - left

      // TODO not sure wether we want to use next
      // val (ub_, decreases_) = ubAndDecreaseFromTest(next)
      // (ub && ub_, Plus(decreases, decreases_))

      (ub, decreases)

    case Le(left, right) :: next =>
      val ub = left <= right + One
      val decreases = right + One - left
      (ub, decreases)

    case Gt(left, right) :: next =>
      val ub = right <= left
      val decreases = left - right
      (ub, decreases)

    case Ge(left, right) :: next =>
      val ub = right <= left + One
      val decreases = left + One - right
      (ub, decreases)

    case head :: next =>
      ubAndDecreaseFromTest(next)

    case Nil =>
      (True, Zero)
  }

  def checkEarlierValueOf(
      counters: Map[Var, Counter],
      current: Expr,
      rho: Map[Var, Var]
  ): Expr = {
    val result = isEarlierValueOf(counters, current, rho)
    result getOrElse True
  }

  def tryEarlierValuesOf(
      counters: Map[Var, Counter],
      current: List[Expr],
      rho: Map[Var, Var]
  ): List[Expr] = {
    for (
      expr <- current;
      phi <- isEarlierValueOf(counters, expr, rho)
    )
      yield phi
  }

  def checkEarlierValuesOf(
      counters: Map[Var, Counter],
      current: List[Expr],
      rho: Map[Var, Var]
  ): Expr = {
    val result = isEarlierValuesOf(counters, current, rho)
    result getOrElse True
  }

  def isEarlierValuesOf(
      counters: Map[Var, Counter],
      current: List[Expr],
      rho: Map[Var, Var]
  ): Option[Expr] = {
    val phis =
      for (
        expr <- current;
        phi <- isEarlierValueOf(counters, expr, rho)
      )
        yield phi

    if (current.length == phis.length) {
      Some(And(phis))
    } else {
      None
    }
  }

  def isEarlierValueOf(
      counters: Map[Var, Counter],
      current: Expr,
      rho: Map[Var, Var]
  ): Option[Expr] = {
    current match {
      case _: Lit =>
        Some(True)

      case i: Var if counters contains i =>
        isEarlierValueOf(counters(i), i, rho)

      case App(inst, args) =>
        isEarlierValuesOf(counters, args, rho)

      case _ =>
        None
    }
  }

  def counters(
      states: List[Path],
      states_ : List[Path],
      mod: List[Var]
  ): Map[Var, Counter] = {
    val pairs =
      for (
        i <- mod if i.typ == Sort.int;
        result <- counter(states, states_, i)
      ) yield result

    Map(pairs: _*)
  }

  def counter(
      states: List[Path],
      states_ : List[Path],
      i: Var
  ): Option[(Var, Counter)] = {
    val is = states map (_ lookup i)
    val init = is.distinct match {
      case List(i0) =>
        Some(i0)
      case _ =>
        None
    }

    val is_ = states_ map (_ lookup i) filter { i_ =>
      i_ != i
    }

    // collect
    val step = is_.distinct match {
      case List(Plus(List(`i`, Lit(step: BigInt, _)))) =>
        Some(step)
      case List(Plus(List(Lit(step: BigInt, _), `i`))) =>
        Some(step)
      case List(Minus(`i`, Lit(step: BigInt, _))) =>
        Some(-step)
      //   case List(`i`) =>
      //     Some(BigInt(0))
      case _ =>
        None
    }

    (init, step) match {
      case (Some(init), Some(step)) =>
        Some(i -> Counter(init, step))
      case _ =>
        None
    }
  }
}

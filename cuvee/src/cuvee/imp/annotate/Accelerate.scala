package cuvee.imp.annotate

import cuvee.SetOps
import cuvee.pure._
import cuvee.imp.Path

case class Counter(init: Expr, step: BigInt)

object Accelerate {
  val plus_one = BigInt(1)
  val minus_one = BigInt(-1)

  def isEarlierValueOf(counter: Counter, i: Var, now: Expr): Option[Expr] = {
    counter match {
      case Counter(init, `plus_one`) =>
        Some(init <= now && now < i)

      case Counter(init, `minus_one`) =>
        Some(i < now && now <= init)

      case _ =>
        None
    }
  }

  def checkEarlierValueOf(counters: Map[Var, Counter], expr: Expr, now: Expr): Expr = {
    val result = isEarlierValueOf(counters, expr, now)
    result getOrElse True
  }

  def isEarlierValueOf(counters: Map[Var, Counter], expr: Expr, now: Expr): Option[Expr] =
    (expr, now) match {
      case (_: Lit, _: Lit) =>
        require(expr == now)
        Some(True)

      case (i: Var, _: Var) if counters contains i =>
        isEarlierValueOf(counters(i), i, now)

      case (App(inst, args), App(_, nows)) =>
        val phis =
          for (
            (arg, now) <- args zip nows;
            phi <- isEarlierValueOf(counters, arg, now)
          )
            yield phi

        if (args.length == phis.length) {
          Some(And(phis))
        } else {
          None
        }

      case _ =>
        None
    }

  def counters(states: List[Path], states_ : List[Path], mod: List[Var]): Map[Var, Counter] = {
    val pairs =
      for (
        i <- mod if i.typ == Sort.int;
        result <- counter(states, states_, i)
      ) yield result

    Map(pairs: _*)
  }

  def counter(states: List[Path], states_ : List[Path], i: Var): Option[(Var, Counter)] = {
    val is = states map (_ lookup i)
    val init = is.distinct match {
      case List(i0) =>
        Some(i0)
      case _ =>
        None
    }

    val is_ = states_ map (_ lookup i)
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

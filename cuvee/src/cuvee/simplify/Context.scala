package cuvee.simplify

import cuvee.pure._
import cuvee.util.UnionFind
import cuvee.util.Fix
import cuvee.util.Name

case class Context(
    polarity: Option[Boolean],
    fixed: Set[Var],
    bound: Set[Var],
    pos: List[Expr],
    neg: List[Expr],
    su: Map[Var, Expr], // trivial substitutions
    eq: Map[Var, Expr], // unsolved equations
    rules: Map[Fun, List[Rule]],
    constrs: Set[Fun],
    depth: Int = 0,
    repeat: Int = 0,
    arith: Boolean = true
) {
  def vars =
    fixed ++ bound

  def free =
    pos.free ++ neg.free ++ su.keys ++ eq.keys ++ Expr.free(su) ++ Expr.free(eq)

  def flip =
    polarity match {
      case None           => this
      case Some(polarity) => copy(polarity = Some(!polarity))
    }

  def unpolar =
    copy(polarity = None)

  def noArith =
    copy(arith = false)

  def isAssumption =
    polarity == Some(false)

  def isUnpolar =
    polarity == None

  def assms =
    pos ++ Not(neg) // note: neg does not have outer negations

  def exists(xs: List[Var]) =
    polarity match {
      case Some(true) => copy(bound = bound ++ xs)
      case _          => copy(fixed = fixed ++ xs)
    }

  def forall(xs: List[Var]) =
    polarity match {
      case Some(false) => copy(bound = bound ++ xs)
      case _           => copy(fixed = fixed ++ xs)
    }

  def isTrivial =
    (pos contains False) || (neg contains True)

  def recurse =
    copy(depth = depth + 1)

  def again =
    copy(repeat = repeat + 1)
}

object Context {
  // Note: requires that the formula over which we run has been normalized already by Clause.flatten,
  // we don't introduce new bound variables etc to the context here,
  // rather, just expand some simple propositional structure.
  def assuming(
      ctx: Context,
      pos: List[Expr] = Nil,
      neg: List[Expr] = Nil
  ): Context = {
    (pos, neg) match {
      case (Nil, Nil) =>
        ctx

      case (True :: pos, neg) =>
        assuming(ctx, pos, neg)

      case (pos, False :: neg) =>
        assuming(ctx, pos, neg)

      case (Eq(x: Var, y: Var) :: pos, neg) if x == y =>
        assuming(ctx, pos, neg)

      case (And(phis) :: pos, neg) =>
        assuming(ctx, phis ++ pos, neg)

      case (pos, Imp(phi, psi) :: neg) =>
        assuming(ctx, phi :: pos, psi :: neg)

      case (pos, Or(phis) :: neg) =>
        assuming(ctx, pos, phis ++ neg)

      case (Not(phi) :: pos, neg) =>
        assuming(ctx, pos, phi :: neg)

      case (pos, Not(phi) :: neg) =>
        assuming(ctx, phi :: pos, neg)

      case (Eq(x: Var, y: Var) :: pos, neg) =>
        val ctx_ = ctx.copy(su = ctx.su + (x -> y))
        assuming(ctx_, pos, neg)

      case (Eq(x: Var, y: Lit) :: pos, neg) =>
        require(!(ctx.su contains x), "unhandled cases with multiple equations for " + x)
        val ctx_ = ctx.copy(su = ctx.su + (x -> y))
        assuming(ctx_, pos, neg)

      case (Eq(y: Lit, x: Var) :: pos, neg) =>
        require(!(ctx.su contains x), "unhandled cases with multiple equations for " + x)
        val ctx_ = ctx.copy(su = ctx.su + (x -> y))
        assuming(ctx_, pos, neg)

      case (Eq(x: Var, e) :: pos, neg) =>
        require(!(ctx.eq contains x), "unhandled cases with multiple equations for " + x)
        val ctx_ = ctx.copy(eq = ctx.eq + (x -> e))
        assuming(ctx_, pos, neg)

      case (Eq(e, x: Var) :: pos, neg) =>
        require(!(ctx.eq contains x), "unhandled cases with multiple equations for " + x)
        val ctx_ = ctx.copy(eq = ctx.eq + (x -> e))
        assuming(ctx_, pos, neg)

      case (phi :: pos, neg) =>
        require(phi.typ == Sort.bool)
        val ctx_ = ctx.copy(pos = ctx.pos ++ List(phi))
        assuming(ctx_, pos, neg)

      case (pos, phi :: neg) =>
        require(phi.typ == Sort.bool)
        val ctx_ = ctx.copy(neg = ctx.neg ++ List(phi))
        assuming(ctx_, pos, neg)
    }
  }

  def eqs(ctx: Context) = {
    val pairs = ctx.pos collect {
      case Eq(x @ Var(Name(_, None), _), y: Var) => (x, y)
      case Eq(y: Var, x @ Var(Name(_, None), _)) => (x, y)
      case Eq(x: Var, e)                         => (x, e)
      case Eq(e, x: Var)                         => (x, e)
    }

    val (xs, _) = pairs.unzip

    val deps = pairs map { case (x, e) =>
      (x, e.free)
    }

    val (order, sccs, result) = Fix.tc(deps)

    var su: Map[Var, Expr] = Map()

    if (pairs.nonEmpty) {
      // println("equations!")
      // println("from: " + pairs)
      // println("deps: " + deps)
      // println(order)
      // println(sccs)
      // println(result)
      // println()

      var todo = xs.toSet

      for (x <- order if todo contains x) {
        val rec = result(x) contains x
        val es = pairs collect { case (`x`, e) => e }
        val once = es.length == 1

        if (!rec && once) {
          val List(e) = es
          su += (x -> e)
          todo -= x
        } else {}
      }
    }

    (su)
  }
}

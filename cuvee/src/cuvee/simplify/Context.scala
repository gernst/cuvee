package cuvee.simplify

import cuvee.pure._
import cuvee.util.UnionFind
import cuvee.util.Fix
import cuvee.util.Name

case class Context(
    polarity: Option[Boolean], // polarity wrt. top-level, false=assumptions, true=conclusions
    fixed: Set[Var], // global variables that cannot be instantiated
    bound: Set[Var], // variables that can be instantiated
    pos: List[Expr], // formulas that are assumed true, resp. proved false
    neg: List[Expr], // formulas that are assumed false, resp. proved true
    su: Map[Var, Expr], // trivial substitutions to Var or Lit
    eq: Map[Var, Expr], // unsolved equations, possibly recursive
    rules: Map[Fun, List[Rule]], // rewrite rules to be used
    constrs: Set[Fun], // information about data type constructors (injective and disjoint)
    depth: Int = 0, // nesting level of rewriting to catch cycles
    repeat: Int = 0, // count how many times simplify was called at top-level to catch cycles
    arith: Boolean = true // whether arithmetic expressions have been normalized
) {
  def vars =
    fixed ++ bound

  def free =
    pos.free ++ neg.free ++ su.keys ++ eq.keys ++ Expr.free(su) ++ Expr.free(eq)

  def resolve(expr: Expr): Expr = expr match {
    case x: Var if su contains x =>
      resolve(su(x))
    case x: Var if eq contains x =>
      resolve(eq(x))
    case _ =>
      expr
  }

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

  def canInstantiate(x: Var) =
    polarity match {
      case Some(true)  => bound contains x
      case Some(false) => fixed contains x
      case None        => false
    }

  def recurse =
    copy(depth = depth + 1)

  def again =
    copy(repeat = repeat + 1)
}

object Context {
  def assigning(ctx: Context, x: Var, e: Expr): Context = {
    val isConst = e.free.isEmpty
    val alreadyReplaces = ctx.su contains x
    val alreadyAssigned = ctx.eq contains x

    // Note: neither e nor su(x) nor eq(e) can be another variable
    if (isConst) {
      // look at ctx.su
      if (!alreadyReplaces) {
        ctx.copy(su = ctx.su + (x -> e))
      } else {
        val phi = Eq(ctx.su(x), e)
        ctx.copy(pos = ctx.pos ++ List(phi))
      }
    } else {
      // look at ctx.eq
      if (!alreadyAssigned) {
        ctx.copy(eq = ctx.eq + (x -> e))
      } else {
        val phi = Eq(ctx.eq(x), e)
        ctx.copy(pos = ctx.pos ++ List(phi))
      }
    }
  }

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

      case (Eq(x: Var, e) :: pos, neg) =>
        val ctx_ = assigning(ctx, x, e)
        assuming(ctx_, pos, neg)

      case (Eq(e, x: Var) :: pos, neg) =>
        val ctx_ = assigning(ctx, x, e)
        assuming(ctx_, pos, neg)

      case (phi :: pos, neg) =>
        require(phi.typ == Sort.bool, "not a boolean: " + phi)
        val ctx_ = ctx.copy(pos = ctx.pos ++ List(phi))
        assuming(ctx_, pos, neg)

      case (pos, phi :: neg) =>
        require(phi.typ == Sort.bool, "not a boolean: " + phi)
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

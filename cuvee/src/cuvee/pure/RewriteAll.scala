package cuvee.pure

import cuvee.error
import cuvee.backtrack
import cuvee.toControl
import cuvee.sexpr.Syntax
import cuvee.smtlib.Assert

object RewriteAll {
  val MaxDepth = 20

  def rewriteAll(rule: Rule, rules: Map[Fun, List[Rule]]): List[Rule] = {
    val Rule(lhs, rhs, cond, avoid) = rule
    for (
      lhs_ <- rewriteAll(lhs, rules);
      rhs_ <- rewriteAll(rhs, rules);
      cond_ <- rewriteAll(cond, rules)
    )
      yield Rule(lhs_, rhs_, cond_, avoid)
  }

  def rewriteAll(
      expr: Expr,
      rules: Map[Fun, List[Rule]],
      depth: Int = 0
  ): List[Expr] = {
    expr match {
      case self if depth > MaxDepth =>
        error("max rewriting depth reached " + self)
      case self @ App(inst, args) =>
        // val indent = "  " * depth
        // println(indent + "rewrite " + expr)
        // println(indent + "  ~~>  " + rhs_)
        val exprs_ = cuvee.trace("rewriting: " + self) {
          for (
            args_ <- rewritesAll(args, rules, depth);
            expr_ <- appAll(App(inst, args_), inst.fun, rules, depth)
          )
            yield expr_
        }
        // println(indent + "    ~~> " + exprs_.mkString(" "))
        exprs_
      case _ =>
        List(expr)
    }
  }

  def rewritesAll(
      exprs: List[Expr],
      rules: Map[Fun, List[Rule]],
      depth: Int
  ): List[List[Expr]] = exprs match {
    case Nil =>
      List(Nil)
    case expr :: rest =>
      for (
        expr_ <- rewriteAll(expr, rules, depth);
        rest_ <- rewritesAll(rest, rules, depth)
      )
        yield expr_ :: rest_
  }

  def appAll(
      expr0: Expr,
      fun: Fun,
      // args: List[Expr],
      rules: Map[Fun, List[Rule]],
      depth: Int
  ): List[Expr] = {
    if (rules contains fun) {
      // val indent = "  " * depth
      // println(indent + "applying " + expr0)
      val exprs2 =
        for (
          rule <- rules(fun);
          expr1 <- rewriteAll(expr0, fun, rule, depth);
          expr2 <- rewriteAll(expr1, rules, depth + 1)
        )
          yield expr2
      // require(result.nonEmpty, "no rewriting result for: " + expr0)
      if (exprs2.nonEmpty) exprs2 else List(expr0)
    } else {
      List(expr0)
    }
  }

  def rewriteAll(
      expr: Expr,
      fun: Fun,
      rule: Rule,
      depth: Int
  ): List[Expr] = {
    val Rule(pat @ App(inst, _), rhs, cond, avoid) = rule

    try {
      val (ty, su) = Expr.bind(pat, expr)

      val _cond = cond // simplify(cond subst env, ctx, st)
      if (_cond != True)
        backtrack("side-condition not satisfied " + _cond)

      val dont = avoid exists { case (a, b) =>
        (a subst su) == (b subst su)
      }

      if (dont) {
        // println("  avoiding cycle for " + expr + " via rule " + rule)
        Nil
      } else {
        val rhs_ = rhs inst (ty, su)
        // println("  "*depth + rhs + " ~> " + rhs_)
        List(rhs_)
        /* val self = List(rhs_)
            val rec = cuvee.trace("  via " + rule) {
              rewriteAll(rhs_, rules, depth + 1)
            }
            println(indent + "  ~~>' " + rec.mkString(" "))
            val others = rewriteAll(expr, fun, rest, rules, depth)
            println(indent + "  ~~>* " + others.mkString(" "))
            // val all = self ++ rec ++ other
            val all = rec ++ others // here keep only fully rewritten terms
            all.distinct */
      }
    } catch { // Control#or is shadowed by Expr#or
      case arse.Backtrack(_) =>
        Nil
    }
  }

  /* def rewriteAll(
      expr: Expr,
      fun: Fun,
      todo: List[Rule],
      rules: Map[Fun, List[Rule]],
      depth: Int
  ): List[Expr] = {
    todo match {
      case Nil =>
        List(expr)

      case (rule @ Rule(pat @ App(inst, _), rhs, cond, avoid)) :: rest =>
        try {
          val (ty, su) = Expr.bind(pat, expr)

          val _cond = cond // simplify(cond subst env, ctx, st)
          if (_cond != True)
            backtrack("side-condition not satisfied " + _cond)

          val dont = avoid exists { case (a, b) =>
            (a subst su) == (b subst su)
          }

          if (dont) {
            println("avoiding cycle for " + expr)
            rewriteAll(expr, fun, rest, rules, depth)
          } else {
            val indent = "  " * depth
            val rhs_ = rhs subst (ty, su)
            println(indent + "rewrite " + expr)
            println(indent + "  ~~>  " + rhs_)
            val self = List(rhs_)
            val rec = cuvee.trace("  via " + rule) {
              rewriteAll(rhs_, rules, depth + 1)
            }
            println(indent + "  ~~>' " + rec.mkString(" "))
            val others = rewriteAll(expr, fun, rest, rules, depth)
            println(indent + "  ~~>* " + others.mkString(" "))
            // val all = self ++ rec ++ other
            val all = rec ++ others // here keep only fully rewritten terms
            all.distinct
          }
        } catch { // Control#or is shadowed by Expr#or
          case arse.Backtrack(_) =>
            rewriteAll(expr, fun, rest, rules, depth)
        }

      case rule :: _ =>
        error("invalid rewrite rule: " + rule)
    }
  } */
}

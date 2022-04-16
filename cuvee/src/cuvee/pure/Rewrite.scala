package cuvee.pure

import cuvee.error
import cuvee.backtrack
import cuvee.toControl
import cuvee.sexpr.Syntax
import cuvee.smtlib.Assert

case class Rule(
    lhs: Expr,
    rhs: Expr,
    cond: Expr = True,
    avoid: List[(Expr, Expr)] = Nil
) extends Syntax {
  require(
    lhs.typ == rhs.typ && cond.typ == Sort.bool,
    "rule not type correct"
  )

  val vars = lhs.free.toList

  def canFlip = rhs match {
    case _: App =>
      lhs.free subsetOf rhs.free
    case _ =>
      false
  }

  def flip = {
    require(canFlip, "cannot flip rule: " + this)
    Rule(rhs, lhs, cond, avoid)
  }

  def maybeFlip = {
    if (canFlip)
      Some(Rule(rhs, lhs, cond, avoid))
    else
      None
  }

  def fun = {
    val App(inst, _) = lhs
    inst.fun
  }

  val toExpr =
    (vars, cond) match {
      case (Nil, True) => Eq(lhs, rhs)
      case (_, True)   => Forall(vars, Eq(lhs, rhs))
      case (Nil, _)    => Imp(cond, Eq(lhs, rhs))
      case _           => Forall(vars, Imp(cond, Eq(lhs, rhs)))
    }

  def sexpr = toExpr

  def cmd = Assert(toExpr)

  override def toString = {
    var res = lhs + " = " + rhs
    var pres = And.flatten(cond)
    pres ++= avoid map { case (x, e)  => (x !== e) }

    if (pres.nonEmpty)
      res += " if " + And(pres)

    res
  }
}

object Rewrite {
  val MaxDepth = 10

  def rewrite(rule: Rule, rules: Map[Fun, List[Rule]]): Rule = {
    val Rule(lhs, rhs, cond, avoid) = rule
    val lhs_ = rewrite(lhs, rules)
    val rhs_ = rewrite(rhs, rules)
    val cond_ = rewrite(cond, rules)
    val avoid_ = avoid map { case (x, e) => (x, rewrite(e, rules)) }
    Rule(lhs_, rhs_, cond_, avoid_)
  }

  def rewriteAll(rule: Rule, rules: Map[Fun, List[Rule]]): List[Rule] = {
    val Rule(lhs, rhs, cond, avoid) = rule
    for (
      lhs_ <- rewriteAll(lhs, rules);
      rhs_ <- rewriteAll(rhs, rules);
      cond_ <- rewriteAll(cond, rules)
    )
      yield Rule(lhs_, rhs_, cond_, avoid)
  }

  def rewrite(expr: Expr, rules: Map[Fun, List[Rule]], depth: Int = 0): Expr = {
    expr bottomup {
      case self if depth > MaxDepth =>
        error("max rewriting depth reached " + self)

      case self @ App(inst, args) =>
        app(self, inst.fun, args, rules, depth)

      case self =>
        self
    }
  }
  
  def rewrites(
      exprs: List[Expr],
      rules: Map[Fun, List[Rule]],
      depth: Int = 0
  ): List[Expr] = {
    exprs map (rewrite(_, rules, depth))
  }

  def app(
      expr: Expr,
      fun: Fun,
      args: List[Expr],
      rules: Map[Fun, List[Rule]],
      depth: Int
  ): Expr = {
    if (rules contains fun) {
      val _expr = rewrite(expr, fun, rules(fun), rules, depth)
      _expr
    } else {
      expr
    }
  }

  var k = 0

  def rewrite(
      expr: Expr,
      fun: Fun,
      todo: List[Rule],
      rules: Map[Fun, List[Rule]],
      depth: Int
  ): Expr = {
    todo match {
      case Nil =>
        expr

      case rule @ Rule(pat @ App(inst, _), rhs, cond, avoid) :: rest =>
        require(
          fun == inst.fun,
          "inconsistent rewrite rule index: " + fun + " has rule " + rule
        )
        try {
          val (ty, su) = Expr.bind(pat, expr)

          val _cond = cond // simplify(cond subst env, ctx, st)
          if (_cond != True)
            backtrack("side-condition not satisfied " + _cond)

          val dont = avoid exists { case (a, b) =>
            val _a = a subst su
            val _b = b subst su
            // println(rule)
            // println("checking cycle " + _a + " and " + _b + " in " + env)
            val r = _a.toString == _b.toString // HACK!!
            if (r && _a != _b)
              println(
                "cycle recognized via hack: " + _a + " and " + _b + " in " + su
              )
            r
          }
          if (dont) {
            // println("avoiding cycle for " + expr + " via rule " + rule)
            val res = rewrite(expr, fun, rest, rules, depth)
            // println(res)
            // if (k == 3) ???
            // k += 1
            res
          } else {
            val rhs_ = rhs subst (ty, su)
            // println("rewrite " + expr)
            // println("  ~~> " + rhs_)
            rewrite(rhs_, rules, depth + 1)
          }
        } catch { // Control#or is shadowed by Expr#or
          case arse.Backtrack(_) =>
            rewrite(expr, fun, rest, rules, depth)
        }

      case rule :: _ =>
        error("invalid rewrite rule: " + rule)
    }
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
        val rhs_ = rhs subst (ty, su)
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

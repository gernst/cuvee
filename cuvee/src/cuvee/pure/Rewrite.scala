package cuvee.pure

import cuvee.error
import cuvee.backtrack
import cuvee.toControl
import cuvee.sexpr.Syntax
import cuvee.smtlib.Assert

object Rewrite {
  val MaxDepth = 20

  def rewrite(rule: Rule, rules: Map[Fun, List[Rule]]): Rule = {
    val Rule(lhs, rhs, cond, avoid) = rule
    val lhs_ = rewrite(lhs, rules)
    val rhs_ = rewrite(rhs, rules)
    val cond_ = rewrite(cond, rules)
    val avoid_ = avoid map { case (x, e) => (x, rewrite(e, rules)) }
    Rule(lhs_, rhs_, cond_, avoid_)
  }

  def rewrite(expr: Expr, rules: Map[Fun, List[Rule]], depth: Int = 0): Expr = {
    expr bottomup {
      case self if depth > MaxDepth =>
        println("max rewriting depth reached: " + self)
        self
        // error("max rewriting depth reached " + self)

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
            val _a = a inst (ty, su)
            val _b = b inst (ty, su)
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
            val rhs_ = rhs inst (ty, su)
            // println("  "*depth + "rewrite " + expr)
            // println("  "*depth + "  ~~> " + rhs_)
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
}

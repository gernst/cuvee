package cuvee.pure

import cuvee.error
import cuvee.backtrack
import cuvee.toControl
import cuvee.sexpr.Syntax

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

  def flip = {
    require(lhs.free subsetOf rhs.free, "cannot flip rule: " + this)
    Rule(rhs, lhs, cond, avoid)
  }

  def maybeFlip = {
    if (lhs.free subsetOf rhs.free)
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
  override def toString =
    if (cond == True)
      lhs + " = " + rhs
    else
      lhs + " = " + rhs + " if " + cond
}

object Rewrite {
  val MaxDepth = 10

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
        require(fun == inst.fun, "inconsistent rewrite rule index: " + fun + " has rule " + rule)
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
            println("avoiding cycle for " + expr)
            val res = rewrite(expr, fun, rest, rules, depth)
            println(res)
            if (k == 3) ???
            k += 1
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
}

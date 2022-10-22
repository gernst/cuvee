package cuvee.pure

import cuvee.error
import cuvee.backtrack
import cuvee.sexpr.Syntax
import cuvee.smtlib.Assert
import cuvee.smtlib.Cmd
import cuvee.State
import cuvee.smtlib.DefineFun
import cuvee.util.Fix
import cuvee.smtlib.DeclareFun
import arse.Backtrack

object Rewrite {
  val MaxDepth = 20

  def from(
      cmd: Cmd,
      ok: Set[Fun],
      st: State,
      assert: Boolean,
      define: Boolean
  ): List[Rule] = {
    cmd match {
      case Assert(expr) if assert =>
        Rules.from(expr, ok)
      case DefineFun(name, xs, _, body, rec) if define =>
        val fun = st.funs(name, xs.length)
        Rules.from(fun, xs, body, ok)
      case _ =>
        Nil
    }
  }

  def from(
      cmds: List[Cmd],
      st: State,
      assert: Boolean = true,
      define: Boolean = true
  ): List[Rule] = {
    val ok =
      for (DeclareFun(name, args, res) <- cmds)
        yield st.funs(name, args.length)

    for (
      cmd <- cmds;
      rule <- from(cmd, ok.toSet, st, assert, define)
    )
      yield rule
  }

  def safe(rules: List[Rule], st: State): List[Rule] = {
    val deps = Rewrite.deps(rules)
    println(deps)

    for (
      rule @ Rule(App(Inst(fun, _), pats), rhs, _, _) <- rules
      if /* !(deps(fun) contains fun) && */ decreases(
        fun,
        pats,
        rhs,
        st.constrs
      )
    )
      yield rule
  }

  def decreases(
      fun: Fun,
      pats: List[Expr],
      rhs: Expr,
      constrs: Set[Fun]
  ): Boolean = rhs match {
    case App(Inst(`fun`, _), rec) =>
      val ok = pats.zipWithIndex.exists {
        case (App(inst, args), i) =>
          (constrs contains inst.fun) && (args contains rec(i))
        case _ =>
          false
      }
      if (!ok)
        println("rejecting: " + rhs)
      ok

    case App(_, args) =>
      args forall (decreases(fun, pats, _, constrs))

    case _: Var | _: Lit =>
      true

    case _ =>
      false // add more cases!
  }

  def deps(rules: List[Rule]) = {
    Fix.tc {
      for (rule <- rules)
        yield rule.fun -> rule.rhs.funs
    }
  }

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
            (a inst (ty, su)) == (b inst (ty, su))
          }

          if (dont) {
            // println("avoiding cycle for " + expr + " via rule " + rule)
            val res = rewrite(expr, fun, rest, rules, depth)
            // println(res)
            res
          } else {
            val rhs_ = rhs inst (ty, su)
            // println("  "*depth + "rewrite " + expr)
            // println("  "*depth + "  ~~> " + rhs_)
            rewrite(rhs_, rules, depth + 1)
          }
        } catch {
          case _: Backtrack =>
            rewrite(expr, fun, rest, rules, depth)
        }

      case rule :: _ =>
        error("invalid rewrite rule: " + rule)
    }
  }
}

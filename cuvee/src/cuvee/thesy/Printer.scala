package cuvee.thesy

import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Counter
import cuvee.util.Name

object Printer extends cuvee.util.Printer with Counter {
  import cuvee.smtlib.Printer._

  def lines(any: Any): List[String] = any match {
    case Sort(Con.array, List(a, b)) =>
      parens("->", a, b)

    case Param(name)     => lines(name)
    case Sort(con, Nil)  => lines(con.name)
    case Sort(con, args) => parens2(con.name)(args)

    // ignore this because TheSy does not support defined sorts
    case _: DeclareSort =>
      Nil

    case Lit(a, _)    => just(a)
    case Var(name, _) => lines("?" + name)
    // case Is(arg, fun)          => parens(args("_", "is", fun.name), arg)
    // case Case(pat, expr)       => parens(pat, expr)
    // case Match(expr, cases, _) => parens("match", expr, cases)
    // case LetEq(x, e)           => parens(x, e)
    // case Let(eqs, body)        => parens("let", eqs, body)
    // case Note(expr, attr)      => parens2("!", expr)(attr)
    // case Distinct(exprs)       => parens2("distinct")(exprs)

    case Bind(quant, formals, body, _) =>
      parens(quant.name, formals.asFormals, body)

    // case Const(arg) =>
    //  parens(args("as", "const", arg.typ), arg)

    case App(inst, Nil) =>
      lines(inst)

    case And(phis) => parens2("and")(phis)
    case Or(phis)  => parens2("or")(phis)

    case App(inst, args) =>
      parens2(inst.fun.name)(args)

    case DeclareFun(name, params, args, res) =>
      parens("declare-fun", name, args, res)

    case DeclareDatatypes(arities, datatypes) =>
      val pairs =
        for (((name, _), dt) <- (arities zip datatypes))
          yield (name, dt)

      pairs flatMap lines

    case (name: Name, Datatype(params, constrs)) =>
      val constrs_ = for ((k, sels) <- constrs) yield {
        k.name :: (sels map (_.res))
      }

      parens("datatype", name, params, constrs_)

    case Assert(phi) =>
      phi match {
        case Forall(xs, Eq(lhs, rhs)) =>
          val fwd = parens("=>", "rule" + next, lhs, rhs)
          val bkw = parens("=>", "rule" + next, rhs, lhs)
          fwd ++ bkw
        case Clause(xs, ant, Eq(lhs, rhs)) =>
          parens("=>", "rule" + next, Imp(And(ant), Eq(lhs, rhs)))
      }

    case Lemma(phi, tactic, assert) =>
      parens("prove", phi)

    case s: String   => just(s)
    case (a, b)      => printApp(lines(a) ++ lines(b))
    case xs: List[_] => printApp(xs flatMap lines)
  }
}

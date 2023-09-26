package cuvee.thesy

import cuvee.pure._
import cuvee.smtlib._
import cuvee.util.Counter
import cuvee.util.Name

object Printer extends cuvee.util.Printer with Counter {
  def just(any: Any): List[String] =
    List(any.toString)

  def parens(args: Any*) =
    List((args.toList flatMap lines) mkString ("(", " ", ")"))

  def parens2(args: Any*)(rest: List[Any]) =
    List(((args ++ rest).toList flatMap lines) mkString ("(", " ", ")"))

  def lines(any: Any): List[String] = any match {
    case name: Name   => just(name.toLabel)
    case Inst(fun, _) => just(fun.name)

    case Sort(Con.array, List(a, b)) =>
      parens("->", a, b)

    case Param(name)     => lines(name)
    case Sort(con, Nil)  => lines(con.name)
    case Sort(con, args) => parens2(con.name)(args)

    // ignore this because TheSy does not support defined sorts
    // case _: DeclareSort =>
    //   Nil

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
        k.name :: (sels map (_.res)) ::: List(k.res)
      }

      parens("datatype", name, params, constrs_)

    case Assert(phi) =>
      phi match {
        case Forall(xs, Eq(lhs, rhs: Var)) =>
          parens("=>", "rule" + next, lhs, rhs)

        case Forall(xs, Eq(lhs, rhs)) if lhs.free subsetOf rhs.free =>
          val fwd = parens("=>", "rule" + next, lhs, rhs)
          val bkw = parens("=>", "rule" + next, rhs, lhs)
          fwd ++ bkw

        case Forall(xs, Eq(lhs, rhs)) =>
          parens("=>", "rule" + next, lhs, rhs)

        case Clause(xs, Nil, Eq(lhs, rhs)) =>
          parens("=>", "rule" + next, lhs, rhs)

        case Clause(xs, List(True), Eq(lhs, rhs)) =>
          parens("=>", "rule" + next, lhs, rhs)

        case Clause(xs, ant, Eq(lhs, rhs)) =>
          parens("=>", "rule" + next, Imp(And(ant), Eq(lhs, rhs)))
      }

    case Lemma(phi, tactic, assert) =>
      parens("prove", phi)

    case s: String   => just(s)
    case (a, b)      => parens(lines(a) ++ lines(b): _*)
    case xs: List[_] => parens(xs flatMap lines: _*)
  }
}

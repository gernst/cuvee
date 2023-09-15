package cuvee.lemmas.deaccumulate

import cuvee.pure._
import cuvee.smtlib._
import cuvee.lemmas.Def

// returned by deaccumulate: (Def, Expr, Fun, List[Fun], List[Rule], List[Cond])
trait Cond {
  def formals: List[Var]
  def toExpr: Expr
}

// Heuristic: look for neutral elements of o
case class N(z: Var, o: Fun, b: Fun) extends Cond {
  val formals = List(z)
  def toExpr = Forall(formals, Eq(o(b(), z), z))
}

// Heuristic: define f(formals) := body
case class D(formals: List[Var], f: Fun, body: Expr) extends Cond {
  def toExpr = Forall(formals, Eq(App(f, formals), body))
}

// Assert g ==> l == r to validate some prior instantiation,
// not generated as part of the original query, only during solving
case class A(formals: List[Var], l: Expr, r: Expr, g: Expr) extends Cond {
  def toExpr = Forall(formals, g ==> Eq(l, r))
}

// Heuristic: guess f(args) := body, taken from existing function definition
case class G(formals: List[Var], f: Fun, body: Expr) extends Cond {
  def toExpr = Forall(formals, Eq(App(f, formals), body))
}

// General case for function body b(args): find b so that forall formals. g ==> l == r
case class B(formals: List[Var], b: Fun, args: List[Var], l: Expr, r: Expr, g: Expr) extends Cond {
  def toExpr = Forall(formals, g ==> Eq(l, r))
}

case class Query(
    df: Def,
    args: List[Expr],
    df_ : Def,
    rhs: Expr,
    oplus: Fun,
    funs: List[Fun],
    conds: List[Cond]
) {
  def lhs = App(df.fun, args)
  def lemma = Rule(lhs, rhs)
  def constraints = conds map (_.toExpr)

  def cmds = {
    val decls =
      for (Fun(name, params, args, res) <- funs)
        yield DeclareFun(name, params, args, res)

    val conds =
      for (phi <- constraints)
        yield Assert(phi)

    decls ++ conds
  }

}

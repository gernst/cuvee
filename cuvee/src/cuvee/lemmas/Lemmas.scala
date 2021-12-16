package cuvee.lemmas

import cuvee.fail
import cuvee.pure._
import cuvee.smtlib._
import cuvee.util._
import cuvee.StringOps

case class Norm(
    as: List[(Var, Expr)],
    bs: List[(Var, Expr)],
    cs: List[(Var, Expr)],
    d: Expr
)

object Norm {
  def just(d: Expr): Norm = {
    Norm(Nil, Nil, Nil, d)
  }
}

case class Case(
    xs: List[Var],
    args: List[Expr],
    guard: List[Expr],
    rhs: Norm
)

case class Def(fun: Fun, cases: List[Case])

object test extends Run(Lemmas, "examples/list-defs.smt2")

object Lemmas extends Main {
  import Split._

  var eqs: Map[Fun, Expr] = Map()

  def main(args: Array[String]): Unit = {
    for (file <- args)
      run(file)
  }

  def run(file: String) {
    val (cmds, st) = parse(file)

    val eqs0 =
      for (
        Assert(expr) <- cmds;
        eq <- rw(expr, st)
      )
        yield eq

    val eqs1 =
      for ((fun, stuff) <- eqs0.groupBy(_._1))
        yield {
          val (_, cases) = stuff.unzip
          Def(fun, cases)
        }

    for (df <- eqs1) {
      show(df)

      val (df_, dfs_a) = ana(df, st)
      show(df_)
      for (df_a <- dfs_a)
        show(df_a)
    }
  }

  def ana(df: Def, st: State): (Def, List[Def]) = {
    val Def(f, cases) = df
    val params = f.params
    val types = f.args

    val nil = st funs "nil"
    val cons = st funs "cons"

    val k = types.length

    val fs =
      for ((res, i) <- types.zipWithIndex)
        yield Fun(f.name + "_a" __ i, params, types, Sort.list(res))

    val acs =
      for (cs <- cases)
        yield ana(f, fs, cs, nil, cons, st)

    val acs_ = acs.transpose

    val df_a =
      for ((f, cs) <- fs zip acs_)
        yield Def(f, cs)

    val at = fs map (_.res)
    val f_ = Fun(f.name + "'", f.params, f.args ++ at, f.res)

    val cases_ =
      for (Case(xs, args, guard, Norm(as, bs, cs, d)) <- cases)
        yield bs match {
          case Nil =>
            val as_ =
              for (_ <- fs)
                yield App(nil, Nil)
            Case(xs, args ++ as_, guard, Norm(Nil, Nil, cs, d))

          case List((y, App(`f`, _, es))) =>
            val ar_as_ =
              for ((a, _) <- as)
                yield {
                  val ar = Var(a.name + "s", Sort.list(a.typ), a.index)
                  ar -> App(cons, List(a, ar))
                }
            val (ar, as_) = ar_as_.unzip
            val bs_ = List((y, App(f_, es ++ ar)))
            Case(xs, args ++ as_, guard, Norm(Nil, bs_, cs, d))
        }

    (Def(f_, cases_), df_a)
  }

  def ana(
      f: Fun,
      fs: List[Fun],
      cs: Case,
      nil: Fun,
      cons: Fun,
      st: State
  ): List[Case] = {
    val Case(xs, args, guard, rhs) = cs
    val as = rhs.as

    val n = rhs.bs.length
    require(n == 0 || n == 1, "non-linear recursion in " + f)

    if (n == 1) {
      require(
        fs.length == rhs.as.length,
        "invalid number of a-variables, expected " + fs.length + ", but have " + rhs.as
      )

      val List((y, App(_, _, args_))) = rhs.bs

      for ((fa, (x, a)) <- fs zip as)
        yield {
          val y_ = Var(y.name, fa.res, y.index)
          val b = App(fa, args_)
          val d = App(cons, List(x, y_))
          Case(xs, args, guard, Norm(as, List(y_ -> b), Nil, d))
        }
    } else {
      for (_ <- fs)
        yield {
          val d = App(nil, Nil)
          Case(xs, args, guard, Norm(as, Nil, Nil, d))
        }
    }
  }

  def show(df: Def) {
    val Def(fun, cases) = df
    println(fun)
    for (Case(xs, args, guard, Norm(as, bs, cs, d)) <- cases) {
      print("  case " + args.mkString("(", ", ", ")"))
      if (guard.nonEmpty)
        print(" if " + guard.mkString(" /\\ "))
      println(" -> ")
      for ((x, e) <- as)
        println("    let " + x + " = " + e)
      for ((x, e) <- bs)
        println("    let " + x + " = " + e)
      for ((x, e) <- cs)
        println("    let " + x + " = " + e)
      println("    in  " + d)
    }
    println()
  }
}

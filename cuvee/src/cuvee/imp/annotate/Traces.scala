package cuvee.imp.annotate

import cuvee.util.Counter
import cuvee.imp._
import cuvee.pure._
import cuvee.imp.traces._
import cuvee.State
import cuvee.smtlib.Cmd
import cuvee.Cuvee
import cuvee.util.Run
import cuvee.util.Name
import scala.collection.immutable
import cuvee.smtlib.DeclareSort
import cuvee.smtlib.DeclareFun

object Traces extends Annotate(ExecNoLoops) {
  override def preamble(state: State) = {
    val (cmds, _) = cuvee.boogie.parse("cuvee/src/cuvee/imp/traces.bpl")
    state.add(cmds) // make the commands visible in this stage's state!
    cmds
  }

  def while_(
      state: State,
      paths: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (List[Cmd], Paths, Prog) = {
    object Current extends Sugar.unary(state.funs("current", 1))
    object Counter extends Sugar.unary(state.funs("counter", 1))

    val mod = body.mod
    val read = body.read

    val vars = test.free ++ mod ++ read
    val xs = vars.toList

    val (cmds_, before, after, body_) =
      iter(state, paths, xs, test = True, body, term, inv, sum, frames)

    // prepare variables:
    // #k <- counter(#n)
    // ws are all regular modified variables
    // zs are all nondet variables

    val k = Expr.fresh("#k", Sort.int)
    val n = Expr.fresh("#n", Sort.int)

    val ws = mod.toList

    val zs =
      for (path <- after.running; y <- path.fresh)
        yield y

    val tr =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(k :: ws))
        yield (x, Var(Name("@" + name, index), Sort.trace(typ)))

    val nd =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(zs))
        yield (x, Var(Name("?" + name, index), Sort.trace(typ)))

    val su = tr ++ nd

    val inv_counter = List(
      Eq(su(k), Counter(n)),
      invariant(k, su, mod ++ zs, test, after.breaked ++ after.returned)
    )

    val inv_traces =
      for (x <- ws)
        yield Eq(su(x), trace(x, k, su, mod ++ zs, after.running))

    val inv_current =
      for (x <- ws)
        yield Eq(x, Current(su(x)))

    val fresh = k :: n :: tr(k) :: (ws map tr) ::: (zs map nd)
    val inv_ = Exists(fresh, And(inv_counter ++ inv_traces ++ inv_current)) note "free"

    val prog_ = While(test, body_, term, inv_, sum, frames)
    val paths_ = exec.spec(paths, ws, inv_, inv_ && !test)

    (cmds_, paths_, prog_)
  }

  def invariant(k: Var, su: Map[Var, Expr], vars: Set[Var], test: Expr, stopped: List[Path]) = {
    val avoid =
      for (path <- stopped)
        yield !And(path.constraints)

    val cond = And(test :: avoid)
    val ys = cond.free & vars

    val eqs =
      for (y <- ys.toList)
        yield LetEq(y, su(y))

    Invariant(eqs, cond)
  }

  def trace(x: Var, k: Var, su: Map[Var, Expr], vars: Set[Var], running: List[Path]) = {
    val ys =
      for (
        path <- running;
        rhs = path lookup x;
        y <- ((path.constraints.free ++ rhs.free) - x) & vars
      )
        yield y

    val eqs1 =
      List(LetEq(k, su(k)))

    val eqs2 =
      for (y <- ys.distinct)
        yield LetEq(y, su(y))

    // val formals =
    //   if (ys.isEmpty) eqs1 else eqs2

    val formals =
      eqs1 ++ eqs2

    val updates =
      for (path <- running) yield {
        val constraints = path.constraints
        val rhs = path lookup x
        Update(And(constraints), rhs)
      }

    Trace(init = Old(x), formals, acc = x, updates)
  }
}

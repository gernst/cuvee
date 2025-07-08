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

object Range extends Sugar.ternary(Fun.range)
object Current extends Sugar.binary(Fun.current)
object Earlier extends Sugar.binary(Fun.earlier)

object Traces extends Annotate(ExecNoLoops) {
  override def preamble(state: State) = {
    val (cmds, _) = cuvee.boogie.parse("cuvee/src/cuvee/imp/traces.bpl")
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
    // object Earlier extends Sugar.binary(state.funs("earlier", 2))
    val mod = body.mod
    val read = body.read

    val vars = test.free ++ mod ++ read
    val xs = vars.toList

    val (cmds_, before, after, body_) =
      iter(state, paths, xs, test, body, term, inv, sum, frames)

    // prepare variables:
    // k is a counter that denotes the current loop iteration
    // ws are all regular modified variables
    // zs are all nondet variables

    val k = Expr.fresh("#k", Sort.int)
    val N = Expr.fresh("#N", Sort.int)

    val ws = mod.toList

    val zs =
      for (path <- after.running; y <- path.fresh)
        yield y

    val tr1 =
      Map(k -> Range(Zero, One, N))

    val tr2 =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(ws))
        yield (x, Var(Name("@" + name, index), Sort.trace(typ)))

    val nd3 =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(zs))
        yield (x, Var(Name("?" + name, index), Sort.trace(typ)))

    val su = tr1 ++ tr2 ++ nd3

    val inv_traces =
      for (x <- ws)
        yield Eq(su(x), trace(x, k, su, mod ++ zs, after.running))

    val inv_current =
      for (x <- k :: ws)
        yield Current(x, su(x))

    val fresh = k :: N :: (ws map tr2) ::: (zs map nd3)
    val inv_ = Exists(fresh, And(inv_traces ++ inv_current)) note "free"

    val prog_ = While(test, body_, term, inv_, sum, frames)
    val paths_ = exec.spec(paths, ws, inv_, inv_ && !test)

    (cmds_, paths_, prog_)
  }

  def trace(x: Var, k: Var, su: Map[Var, Expr], vars: Set[Var], running: List[Path]) = {
    val ys =
      for (
        path <- running;
        rhs = path lookup x;
        y <- ((path.constraints.free ++ rhs.free) - x) & vars
      )
        yield y

    val formals =
      if (ys.isEmpty)
        List(LetEq(k, su(k)))
      else
        for (y <- ys.distinct)
          yield LetEq(y, su(y))

    val iteration =
      Iteration(Sequential, formals)

    val updates =
      for (path <- running) yield {
        val constraints = path.constraints
        val rhs = path lookup x
        Update(And(constraints), rhs)
      }

    Trace(init = Old(x), iteration, x, updates)
  }
}

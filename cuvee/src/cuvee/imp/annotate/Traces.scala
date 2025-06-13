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

object Last extends Sugar.unary(Fun.last)

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

    // require(after.breaked.isEmpty, "breaks are currently unsupported")
    // require(after.returned.isEmpty, "returns are currently unsupported")

    val ws = mod.toList

    val zs =
      for (path <- after.running; y <- path.fresh)
        yield y

    val tr =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(ws))
        yield (x, Var(Name("@" + name, index), Sort.trace(typ)))

    val nd =
      for ((x, Var(Name(name, index), typ)) <- Expr.fresh(zs))
        yield (x, Var(Name("?" + name, index), Sort.trace(typ)))

    val su = tr ++ nd

    val inv_guard =
      List(invariant(su, mod ++ zs, after.running))

    val inv_traces =
      for (x <- ws)
        yield Eq(tr(x), trace(x, su, mod ++ zs, after.running))

    val inv_last =
      for (x <- ws)
        yield Eq(x, Last(tr(x)))

    val fresh = su.values.toList
    val inv_ = Exists(fresh, And(inv_guard ++ inv_traces ++ inv_last)) note "free"

    val prog_ = While(test, body_, term, inv_, sum, frames)
    val paths_ = exec.spec(paths, ws, inv_, inv_ && !test)

    (cmds_, paths_, prog_)
  }

  def invariant(su: Map[Var, Expr], vars: Set[Var], running: List[Path]) = {
    val ys =
      for (
        path <- running;
        y <- path.constraints.free & vars
      )
        yield y

    val formals =
      for (y <- ys.distinct)
        yield LetEq(y, su(y))

    val iteration =
      Iteration(Sequential, formals)

    val paths =
      for (path <- running)
        yield And(path.constraints)

    Invariant(iteration, Or(paths))
  }

  def trace(x: Var, su: Map[Var, Expr], vars: Set[Var], running: List[Path]) = {
    val ys =
      for (
        path <- running;
        rhs = path lookup x;
        y <- ((path.constraints.free ++ rhs.free) - x) & vars
      )
        yield y

    val formals =
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

package cuvee.imp.annotate

import cuvee.pure._
import cuvee.imp._
import cuvee.smtlib.Solver
import cuvee.State

case class Arrays(frame: Boolean, guard: Boolean)
    extends Annotate(ExecNoLoops) {
  def while_(
      state: cuvee.State,
      paths: Paths,
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ) = {
    val mod = body.mod
    val read = body.read

    val (as, ys) = mod.toList partition {
      case a @ Var(_, Sort(Con.array, _)) => true
      case _                              => false
    }

    val vars = test.free ++ mod ++ read
    val xs = vars.toList

    val (cmds, before, after, body_) =
      iter(state, paths, xs, test, body, term, inv, sum, frames)

    val counters = Accelerate.counters(paths.running, after.running, ys)

    // println(paths)
    // println(paths_)
    // println(counters)

    val lbs = Accelerate.lbsFromCounter(counters)
    val (ub, decreases) = Accelerate.ubAndDecreaseFromTest(And.flatten(test))

    val re = Expr.fresh(ys)
    val phi = accelerateWrites(mod, as, ys, re, counters, after.running)

    var phis = lbs ++ List(ub) ++ phi
    if (guard) {
      val psi = accelerateGuard(
        mod,
        as,
        ys,
        re,
        counters,
        test,
        // inv,
        And(inv :: lbs),
        after.breaked ++ after.returned
      )
      phis = phis ++ psi
    }
    val add = And(phis)

    // val props = phis map Prop.from
    // val props_ = Simplify.simplify_(props, Map(), Set())

    val add_ = Simplify.simplify(add, Map(), Set())
    val inv_ = inv && add_
    // Simplify.simplify(And(inv :: lbs) && ub && add, Map(), Set())

    // val inv_ = inv && add

    // require(
    //   after.breaked.isEmpty,
    //   "array acceleration ignores break in loops: " + after.breaked
    // )

    // require(
    //   after.returned.isEmpty,
    //   "array acceleration ignores return in loops"
    // )

    // require(
    //   after.asserted.isEmpty,
    //   "array acceleration ignores asserts in loops"
    // )

    var term_ = term
    if (term == Zero)
      term_ = decreases

    val prog_ = While(test, body_, term_, inv_, sum, frames)
    val paths_ = exec.spec(paths, mod.toList, inv_, inv_ && !test)

    (cmds, paths_, prog_)
  }

  def accelerateGuard(
      mod: Set[Var],
      as: List[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Kounter],
      test: Expr,
      inv: Expr,
      avoid: List[Path]
  ): List[Expr] = {
    val ys_ = ys rename re
    val test_ = test rename re
    val inv_ = inv rename re
    val prems = Accelerate.tryEarlierValuesOf(counters, ys, re)

    val avoids =
      for (Path(fresh, constraints, _, _) <- avoid)
        yield Not(Exists(fresh, And(constraints))) rename re

    // println("avoids: ")
    // avoids foreach println
    val result = Forall(ys_, And(inv_ :: prems) ==> And(test_ :: avoids))
    // println(ys, ys_, prems)
    // println(result)
    List(result)
  }

  def accelerateWrites(
      mod: Set[Var],
      as: List[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Kounter],
      paths: List[Path]
  ): List[Expr] = {
    for (a <- as; inv <- accelerateWrites(mod, ys, re, counters, paths, a))
      yield inv
  }

  def accelerateWrites(
      mod: Set[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Kounter],
      paths: List[Path],
      a: Var
  ): List[Expr] = {
    val x = Expr.fresh("x", dom(a))
    val pairs = equalities(mod, ys, re, counters, paths, a, x)

    val (prems, concls) = pairs.unzip
    val p = And(prems)
    val yes = Or(concls)
    val no = Select(a, x) === Old(Select(a, x))

    if (frame) {
      val phi = Forall(List(x), p ==> yes)
      val psi = Forall(List(x), (Not(p) ==> no))
      List(phi, psi)
    } else {
      val phi = Forall(List(x), p ==> yes)
      List(phi)
    }
  }

  def dom(a: Var) = a match {
    case a @ Var(_, Sort(Con.array, List(t, _))) =>
      t
  }

  def equalities(
      mod: Set[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Kounter],
      paths: List[Path],
      a: Var,
      x: Var
  ) = for (path <- paths if (path lookup a) != a) yield {
    val vars = path.fresh ++ (ys rename re)
    val branch = path.constraint rename re

    val rhs = path lookup a

    // TODO: these two share most of their computations
    val prem = indexEqualities(counters, re, a, x, rhs)
    val concl = assignmentEqualities(mod, counters, re, a, x, rhs)

    val index = Exists(vars, prem)
    val value = Exists(vars, branch && concl)

    (index, value)
  }

  def indexEqualities(
      counters: Map[Var, Kounter],
      re: Map[Var, Var],
      a: Var,
      x: Var,
      rhs: Expr
  ): Expr = rhs match {
    case `a` =>
      False

    case Store(rhs_, key, _) =>
      val now = key rename re
      val earlier = Accelerate.checkEarlierValueOf(counters, key, re)
      val there = indexEqualities(counters, re, a, x, rhs_)
      Ite(x === now, earlier, there)
  }

  def assignmentEqualities(
      mod: Set[Var],
      counters: Map[Var, Kounter],
      re: Map[Var, Var],
      a: Var,
      x: Var,
      rhs: Expr
  ): Expr =
    rhs match {
      case `a` =>
        False

      case Store(rhs_, key, value) =>
        val now = key rename re
        val earlierThis = Accelerate.checkEarlierValueOf(counters, key, re)
        val value_ = maybeOldOtherArrays(mod, value)
        val earlierThat =
          Accelerate.checkEarlierValueOf(counters, value_, re)
        val here = Select(a, x) === (value_ rename re)
        val there = assignmentEqualities(mod, counters, re, a, x, rhs_)
        Ite(x === now, earlierThis && earlierThat && here, there)
    }

  def maybeOldOtherArrays(mod: Set[Var], rhs: Expr): Expr = rhs topdown {
    case Select(b: Var, key) if mod contains b =>
      Select(Old(b), maybeOldOtherArrays(mod, key))
    case expr =>
      expr
  }
}

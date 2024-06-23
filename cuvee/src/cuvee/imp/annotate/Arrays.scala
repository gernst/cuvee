package cuvee.imp.annotate

import cuvee.pure._
import cuvee.imp._
import cuvee.imp.annotate.Accelerate.counter

object Arrays extends Annotate {
  def while_(
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

    val su = Expr.id(test.free ++ mod ++ read)
    val fresh = Nil
    val constraints = List(test, inv)
    val vars = List(su)

    val init = Path(fresh, constraints, vars, List(vars))
    val arbitrary = Paths(List(init))

    val (paths_, body_) = annotate(arbitrary, body)
    val counters = Accelerate.counters(paths.running, paths_.running, ys)

    // println(paths)
    // println(paths_)
    // println(counters)

    val re = Expr.fresh(ys)
    val phi = accelerateWrites(mod, as, ys, re, counters, paths_.running)
    val psi = accelerateGuard(mod, as, ys, re, counters, test, inv)
    val add = And(phi ++ psi)
    val inv_ = Simplify.simplify(inv && add, Map(), Set())
    // val inv_ = inv && add

    val prog_ = While(test, body_, term, inv_, sum, frames)

    val paths__ = exec.spec(paths, mod.toList, inv_, inv_ && !test)

    (paths__, prog_)
  }

  def accelerateGuard(
      mod: Set[Var],
      as: List[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Counter],
      test: Expr,
      inv: Expr
  ): List[Expr] = {
    val ys_ = ys rename re
    val test_ = test rename re
    val inv_ = inv rename re
    val prems = Accelerate.tryEarlierValuesOf(counters, ys, ys_)
    val result = Forall(ys_, And(inv_ :: prems) ==> test_)
    // println(ys, ys_, prems)
    // println(result)
    List(result)
  }

  def accelerateWrites(
      mod: Set[Var],
      as: List[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Counter],
      paths: List[Path]
  ): List[Expr] = {
    for (a <- as; inv <- accelerateWrites(mod, ys, re, counters, paths, a))
      yield inv
  }

  def accelerateWrites(
      mod: Set[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Counter],
      paths: List[Path],
      a: Var
  ): List[Expr] = {
    val x = Expr.fresh("x", dom(a))
    val pairs = equalities(mod, ys, re, counters, paths, a, x)

    val (prems, concls) = pairs.unzip
    val p = Or(prems)
    val yes = Or(concls)
    val no = Select(a, x) === Old(Select(a, x))

    val phi = Forall(List(x), p ==> yes)
    val psi = Forall(List(x), (Not(p) ==> no))

    List(phi, psi)
  }

  def dom(a: Var) = a match {
    case a @ Var(_, Sort(Con.array, List(t, _))) =>
      t
  }

  def equalities(
      mod: Set[Var],
      ys: List[Var],
      re: Map[Var, Var],
      counters: Map[Var, Counter],
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

    val index = Exists(vars, branch && prem)
    val value = Exists(vars, branch && concl)

    (index, value)
  }

  def indexEqualities(
      counters: Map[Var, Counter],
      re: Map[Var, Var],
      a: Var,
      x: Var,
      rhs: Expr
  ): Expr = rhs match {
    case `a` =>
      False

    case Store(rhs_, key, _) =>
      val now = key rename re
      val earlier = Accelerate.checkEarlierValueOf(counters, key, now)
      val there = indexEqualities(counters, re, a, x, rhs_)
      Ite(x === now, earlier, there)
  }

  def assignmentEqualities(
      mod: Set[Var],
      counters: Map[Var, Counter],
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
        val value_ = maybeOldOtherArrays(mod, value)
        val earlier = Accelerate.checkEarlierValueOf(counters, key, now)
        val here = Select(a, x) === (value_ rename re)
        val there = assignmentEqualities(mod, counters, re, a, x, rhs_)
        Ite(x === now, earlier && here, there)
    }

  def maybeOldOtherArrays(mod: Set[Var], rhs: Expr): Expr = rhs topdown {
    case Select(b: Var, key) if mod contains b =>
      Select(Old(b), maybeOldOtherArrays(mod, key))
    case expr =>
      expr
  }

  object exec extends Exec {
    override def while_(
        paths0: Paths,
        test: Expr,
        body: Prog,
        term: Expr,
        inv: Expr,
        sum: Expr,
        frames: List[Frame]
    ): Paths = ???
  }
}

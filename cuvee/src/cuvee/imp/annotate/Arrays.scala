package cuvee.imp.annotate

import cuvee.pure._
import cuvee.imp._

object Arrays extends Annotate[Path] {
  def while_(
      states: States[Path],
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
    val arbitrary = States(List(init))

    val (states_, body_) = annotate(arbitrary, body)
    val counters = Accelerate.counters(states.running, states_.running, ys)

    // println(states)
    // println(states_)
    // println(counters)

    val phi = accelerateWrites(mod, as, ys, counters, states_.running)
    val add = And(phi)
    val inv_ = Simplify.simplify(inv && add, Map(), Set())
    // val inv_ = inv && add

    val prog_ = While(test, body_, term, inv_, sum, frames)

    val states__ = exec.spec(states, mod.toList, inv_, inv_ && !test)

    (states__, prog_)
  }

  def accelerateWrites(
      mod: Set[Var],
      as: List[Var],
      ys: List[Var],
      counters: Map[Var, Counter],
      states: List[Path]
  ): List[Expr] = {
    for (a <- as; inv <- accelerateWrites(mod, ys, counters, states, a))
      yield inv
  }

  def accelerateWrites(
      mod: Set[Var],
      ys: List[Var],
      counters: Map[Var, Counter],
      states: List[Path],
      a: Var
  ): List[Expr] = {
    val x = Expr.fresh("x", dom(a))
    val pairs = equalities(mod, ys, counters, states, a, x)

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
      counters: Map[Var, Counter],
      states: List[Path],
      a: Var,
      x: Var
  ) = for (path <- states if (path lookup a) != a) yield {
    val re = Expr.fresh(ys)

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

  object exec extends Exec[Path] with Exec.WithPath {
    override def while_(
        states0: States[Path],
        test: Expr,
        body: Prog,
        term: Expr,
        inv: Expr,
        sum: Expr,
        frames: List[Frame]
    ): States[Path] = ???
  }
}

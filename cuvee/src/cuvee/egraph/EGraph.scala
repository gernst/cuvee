package cuvee.egraph

import cuvee.pure._
import cuvee.util.Fix

class EGraph {
  self =>
  var hash = Map[ENode, EClass]()
  var todo = Set[EClass]()
  var classes = Set[EClass]()

  def free = hash.keySet collect { case EVar(x) => x }
  def funs = hash.keySet collect { case EApp(inst, _) => inst.fun }

  var debug = false

  object RefuteUnification extends Exception

  def invariants() {
    assert(todo.isEmpty)
    // val nds =
    //   for (ec <- classes; nd <- ec.nodes)
    //     yield nd.canon

    // assert(hash.keySet == nds)

    for (ec <- classes) {
      assert(ec.egraph == this)
    }

    for (ec <- classes; nd <- ec.nodes) {
      // assert(nd.canon == nd, "not canonical: " + nd + " in " + ec)
      assert(lookup(nd) == ec.find)
    }

    for ((nd, ec) <- hash) {
      assert(lookup(nd) == ec.find)
    }
  }

  // descructively replaces a function symbol,
  // g must not occur yet
  def replace(f: Fun, g: Fun) {
    invariants()

    assert(!(funs contains g))
    assert(f.params == g.params)
    assert(f.args == g.args)
    assert(f.res == g.res)

    for (ec <- classes)
      ec.replace(f, g)

    hash =
      for ((nd, ec) <- hash)
        yield (nd.replace(f, g), ec)

    invariants()
  }

  // creates a copy of this graph
  def copy(ecs: EClass*): Seq[EClass] = {
    invariants()

    val that = new EGraph
    var map = Map[EClass, EClass]()

    for (ec <- this.classes) {
      map += (ec -> new EClass(this))
    }

    that.classes =
      for (ec <- classes)
        yield ec.transfer(map)

    that.hash =
      for ((nd, ec) <- hash)
        yield nd.transfer(map) -> map(ec)

    that.invariants()
    
    ecs map map
  }

  def lookup(nd: ENode) = {
    val ec = hash(nd.canon)
    ec.find
  }

  def add(expr: Expr): EClass = expr match {
    case x: Var =>
      add(EVar(x))
    case Lit(any, typ) =>
      add(ELit(any, typ))
    case App(inst, args) =>
      add(EApp(inst, args map add))
    case _ =>
      cuvee.error("cannot add to e-graph: " + expr)
  }

  def merge(lhs: Expr, rhs: Expr): EClass = {
    merge(add(lhs), add(rhs))
  }

  def add(nd_ : ENode): EClass = {
    val nd = nd_.canon

    if (hash contains nd) {
      hash(nd)
    } else {
      val ec = new EClass(this, nd)
      classes += ec

      for (arg <- nd.args)
        arg.parents += nd -> ec

      assert(ec == ec.find)
      hash += (nd -> ec)

      ec
    }
  }

  def merge(ec1_ : EClass, ec2_ : EClass): EClass = {
    val ec1 = ec1_.find
    val ec2 = ec2_.find

    if (debug)
      println("merge " + ec1 + " and " + ec2)

    if (ec1 == ec2) {
      ec1
    } else {
      ec1 union ec2

      todo += ec1 // need to rebuild ec1 later
      if (debug)
        println("delete " + ec2)
      classes -= ec2 // ec2 now obsolete

      ec1
    }
  }

  def rebuild() {
    while (todo.nonEmpty) {
      val now = todo map (_.find)

      todo = Set()

      for (ec <- now)
        repair(ec) // may add some more todos
    }

    invariants()
  }

  def repair(ec: EClass) {
    if (debug)
      println("repair " + ec)

    assert(ec.find == ec)

    for ((pnd, pec) <- ec.parents) {
      hash -= pnd
      hash += (pnd.canon -> pec.find)
    }

    var parents: Map[ENode, EClass] = Map()

    for ((pnd_, pec) <- ec.parents) {
      // assert(pnd.canon == pnd)
      val pnd = pnd_.canon
      if (parents contains pnd)
        merge(pec, parents(pnd))
      parents += pnd -> pec.find
    }

    ec.parents = parents

    if (debug) {
      println("repaired " + ec)
      for (nd <- ec.nodes) {
        assert(nd.canon == nd)
        println("  " + nd)
      }
      println()
    }
  }

  def ematch(
      pat: Expr,
      ec: EClass,
      su: Map[Var, EClass] = Map()
  ): Set[Map[Var, EClass]] = pat match {
    case x: Var if !(su contains x) =>
      Set(su + (x -> ec.find))

    case x: Var if (su contains x) && su(x).find == ec.find =>
      Set(su)

    case _: Var =>
      Set()

    case Lit(any, typ) =>
      for (ELit(`any`, `typ`) <- ec.find.nodes)
        yield su

    case App(inst, pats) =>
      for (
        EApp(`inst`, args) <- ec.find.nodes; // monomorphic only
        su <- ematch(pats, args, su)
      ) yield {
        su
      }
  }

  def ematch(
      pats: List[Expr],
      ecs: List[EClass],
      su0: Map[Var, EClass]
  ): Set[Map[Var, EClass]] = (pats, ecs) match {
    case (Nil, Nil) =>
      Set(su0)

    case (pat :: pats, id :: ecs) =>
      for (
        su1 <- ematch(pat, id, su0);
        su2 <- ematch(pats, ecs, su1)
      )
        yield su2
  }

  def ematch(pat: Expr, ecs: Set[EClass]): Set[(Map[Var, EClass], EClass)] = {
    for (
      ec <- ecs;
      su <- ematch(pat, ec)
    )
      yield (su, ec)
  }

  def ematches(where: Set[EClass], rules: List[Rule]) = {
    for (
      rule @ Rule(lhs, rhs, cond, avoid) <- rules;
      (su, lhs_) <- ematch(lhs, where)
    ) yield {
      val bad = avoid exists { case (a, b) =>
        val a_ = subst(a, su)
        val b_ = add(b)
        a_ == b_ // bad matches are syntactic
      }

      val rhs_ = subst(rhs, su)
      val cond_ = subst(cond, su)
      (bad, rule, su, lhs_, rhs_, cond_)
    }
  }

  def subst(expr: Expr, su: Map[Var, EClass]): EClass = expr match {
    case x: Var if su contains x =>
      su(x)

    case x: Var =>
      add(EVar(x))

    case Lit(any, typ) =>
      add(ELit(any, typ))

    case App(inst, args) =>
      add(EApp(inst, args map (subst(_, su))))
  }

  // if speculate is true then conditional rules are accepted regardless
  // otherwise only applies rewrite rules whose conditions are satisfied
  def rewrite(where: Set[EClass], rules: List[Rule], speculate: Boolean) = {
    var done: Boolean = false
    var conds = Set[EClass]()

    while (!done) {
      done = true

      for ((bad, rule, su, lhs, rhs, cond) <- ematches(where, rules)) {
        var ok = true

        // reject syntactic avoid conditions
        ok = ok && !bad

        // no need to continue if lhs and rhs are already the in same class
        ok = ok && (lhs.find != rhs.find)

        // if we're not allowed to speculate, then check side-cond
        ok = ok && (speculate || cond.isTrue)

        if (ok) {
          merge(lhs, rhs)
          done = false

          // keep track of (nontrivial) speculated conditions
          if (!cond.isTrue)
            conds += cond
        }
      }

      rebuild()
    }

    conds
  }

  def eunify(
      nd1: ENode,
      nd2: ENode,
      constrs: Set[Fun],
      su: Map[Var, ENode] = Map()
  ): Set[Map[Var, ENode]] = (nd1, nd2) match {
    case _ if nd1 == nd2 =>
      Set(Map()) // one trivial solution

    case (EVar(x1), _) if su contains x1 =>
      eunify(su(x1), nd2, constrs, su)

    case (EVar(x1), _) /* if !(nd1 in nd2) */ =>
      Set(su + (x1 -> nd2))

    case (_, _: EVar) =>
      eunify(nd2, nd1, constrs, su)

    case (EApp(Inst(f, _), args1), EApp(Inst(g, _), args2)) if f == g =>
      eunify_classes(args1, args2, constrs, su)

    // here we can say for sure that the current nodes are *not* unifiable,
    // which means that the entire unification we have started is refuted
    case (ELit(any1, typ1), ELit(any2, typ2)) if (any1 != any2) && (typ1 == typ2) =>
      throw RefuteUnification

    case (EApp(Inst(f, _), args1), EApp(Inst(g, _), args2))
        if (constrs contains f) && (constrs contains g) =>
      throw RefuteUnification

    // otherwise, the result is inconclusive and we don't produce a result at all
    case _ =>
      Set()
  }

  def eunify(
      ec1: EClass,
      ec2: EClass,
      constrs: Set[Fun],
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = {
    for (
      nd1 <- ec1.nodes;
      nd2 <- ec2.nodes;
      su1 <- eunify(nd1, nd2, constrs, su0)
    )
      yield su1
  }

  def eunify_classes(
      ecs1: List[EClass],
      ecs2: List[EClass],
      constrs: Set[Fun],
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = (ecs1, ecs2) match {
    case (Nil, Nil) =>
      Set(su0)

    case (ec1 :: ecs1, ec2 :: ecs2) =>
      for (
        su1 <- eunify(ec1, ec2, constrs, su0);
        su2 <- eunify_classes(ecs1, ecs2, constrs, su1)
      )
        yield su2
  }

  def eunify_nodes(
      nds1: List[ENode],
      nds2: List[ENode],
      constrs: Set[Fun],
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = (nds1, nds2) match {
    case (Nil, Nil) =>
      Set(su0)

    case (nd1 :: nds1, nd2 :: nds2) =>
      for (
        su1 <- eunify(nd1, nd2, constrs, su0);
        su2 <- eunify_nodes(nds2, nds2, constrs, su1)
      )
        yield su2
  }

  def extractAll(
      consider: ENode => Boolean = _ => true,
      known: Set[EClass] = Set()
  ): Set[Set[Expr]] = {
    for (ec <- classes)
      yield extract(ec, consider, known)
  }

  def extract(
      ec: EClass,
      consider: ENode => Boolean = _ => true,
      known: Set[EClass] = Set()
  ): Set[Expr] = {
    if (known contains ec) {
      Set()
    } else {
      ec.nodes.filter(consider) flatMap {
        case EVar(x) =>
          Set(x)

        case ELit(any, typ) =>
          Set(Lit(any, typ))

        case EApp(inst, args) =>
          for (args_ <- extract(args, consider, known + ec))
            yield App(inst, args_)
      }
    }
  }

  def extract(
      ids: List[EClass],
      consider: ENode => Boolean,
      known: Set[EClass]
  ): Set[List[Expr]] = ids match {
    case Nil =>
      Set(Nil)

    case ec :: ids =>
      for (
        e <- extract(ec, consider, known);
        es <- extract(ids, consider, known)
      )
        yield e :: es
  }
}

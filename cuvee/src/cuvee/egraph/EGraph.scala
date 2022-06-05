package cuvee.egraph

import scala.collection.mutable

import cuvee.pure._
import scala.annotation.tailrec

class EGraph {
  var debug = false

  val classes = mutable.Map[EId, EClass]()
  val hash = mutable.Map[ENode, EId]()
  val todo = mutable.Set[EId]()

  def lookup(nd: ENode) = {
    val id = hash(nd.canon)
    id.find
  }

  def invariant() {
    for (
      (id, ec) <- classes;
      nd <- ec.nodes
    ) {
      // val lhs = id.find
      // val nd_ = nd.canon
      // val rhs = hash(nd_)
      // if (lhs != rhs) {
      //   println("id*  = " + id.find)
      //   println("nd*# = " + hash(nd_))
      //   println("nd*#*= " + hash(nd_).find)

      //   println("id   = " + id)
      //   println("nd   = " + nd)
      //   println("nd*  = " + nd_)
      //   println("nd#  = " + hash(nd))

      //   for ((id, ec) <- classes) {
      //     println("class " + id)
      //     for (expr <- extract(id))
      //       println("  " + expr)
      //   }
      // }

      // assert(
      //   lhs == rhs,
      //   "node " + nd + " not in canonical form (" + lhs + " vs. " + rhs + ")"
      // )

      assert(lookup(nd) == id.find)
    }

    for ((nd, id) <- hash) {
      assert(lookup(nd) == id.find)
    }
  }

  object EId extends cuvee.util.Counter

  class EId {
    val id = EId.next

    var repr: EId = this

    def find: EId = {
      if (repr != this)
        repr = repr.find // compaction
      repr
    }

    def union(that: EId) { // make this the representant
      that.repr = this
    }

    override def toString = {
      val ec = classes(find)
      if (ec.nodes.size == 1) {
        ec.nodes.head.toString
      } else {
        "$" + find.id
      }
    }
  }

  sealed trait ENode {
    def args: List[EId]
    def canon: ENode
    def children = args map classes
  }

  case class EVar(x: Var) extends ENode {
    def args = Nil
    def canon = this
    override def toString = x.toString
    def in(that: ENode): Boolean = false
  }

  case class ELit(any: Any, typ: Type) extends ENode {
    def args = Nil
    def canon = this
    override def toString = any.toString
  }

  case class EApp(inst: Inst, args: List[EId]) extends ENode {
    def canon = EApp(inst, args map (_.find))

    override def toString = this match {
      case EApp(inst, Nil) =>
        inst.toString
      case _ =>
        inst + args.mkString("(", ", ", ")")
    }
  }

  class EClass(var parents: Map[ENode, EId], var nodes: Set[ENode]) {
    require(nodes.nonEmpty, "an e-class must be nonempty")
  }

  def extracts(
      consider: ENode => Boolean = _ => true,
      known: Set[EId] = Set()
  ): Set[Set[Expr]] = {
    for (id <- classes.keys.toSet[EId])
      yield extract(id, consider, known)
  }

  def extract(
      id: EId,
      consider: ENode => Boolean = _ => true,
      known: Set[EId] = Set()
  ): Set[Expr] =
    if (known contains id.find) {
      Set()
    } else {
      val ec = classes(id.find)

      ec.nodes.filter(consider) flatMap {
        case EVar(x) =>
          Set(x)
        case ELit(any, typ) =>
          Set(Lit(any, typ))
        case EApp(inst, args) =>
          val known_ = known + id.find
          for (args_ <- extract(args, consider, known_))
            yield App(inst, args_)
      }
    }

  def extract(
      ids: List[EId],
      consider: ENode => Boolean,
      known: Set[EId]
  ): Set[List[Expr]] = ids match {
    case Nil =>
      Set(Nil)
    case id :: ids =>
      for (
        e <- extract(id, consider, known);
        es <- extract(ids, consider, known)
      )
        yield e :: es
  }

  def add(expr: Expr): EId = expr match {
    case x: Var =>
      add(EVar(x))
    case Lit(any, typ) =>
      add(ELit(any, typ))
    case App(inst, args) =>
      add(EApp(inst, args map add))
    case _ =>
      cuvee.error("cannot add to e-graph: " + expr)
  }

  def merge(lhs: Expr, rhs: Expr): EId = {
    merge(add(lhs), add(rhs))
  }

  def add(nd_ : ENode): EId = {
    val nd = nd_.canon

    if (hash contains nd) {
      if (debug)
        println("known " + nd)
      hash(nd)
    } else {
      val id = new EId
      val ec = new EClass(Map(), Set(nd))

      classes += id -> ec

      for (arg <- nd.children)
        arg.parents += nd -> id

      hash(nd) = id.find

      if (debug)
        println("new class " + id + ": " + nd)

      id
    }
  }

  def merge(id1_ : EId, id2_ : EId): EId = {
    val id1 = id1_.find
    val id2 = id2_.find

    if (id1 == id2) {
      id1 // compacted now
    } else {
      val ec1 = classes(id1)
      val ec2 = classes(id2)

      id1 union id2

      ec1.parents ++= ec2.parents
      ec1.nodes ++= ec2.nodes

      todo += id1

      if (debug)
        println("del class " + id2)
      classes -= id2

      id1
    }
  }

  def rebuild() {
    while (todo.nonEmpty) {
      val now = todo map (_.find)

      todo.clear()

      for (id <- now)
        repair(id) // may add some more todos
    }

    invariant()
  }

  def repair(id: EId) {
    assert(id.find == id)
    val ec = classes(id)

    for ((pnd, pid) <- ec.parents) {
      hash -= pnd
      hash(pnd.canon) = pid.find
    }

    var parents: Map[ENode, EId] = Map()

    for ((pnd_, pid) <- ec.parents) {
      val pnd = pnd_.canon
      if (parents contains pnd)
        merge(pid, parents(pnd))
      parents += pnd -> pid.find
    }

    ec.parents = parents
  }

  def ematch(
      pat: Expr,
      id: EId,
      su: Map[Var, EId] = Map()
  ): Set[Map[Var, EId]] = pat match {
    case x: Var if !(su contains x) =>
      Set(su + (x -> id))

    case x: Var if (su contains x) && su(x).find == id.find =>
      Set(su)

    case _: Var =>
      Set()

    case Lit(any, typ) =>
      val ec = classes(id.find)

      for (ELit(`any`, `typ`) <- ec.nodes)
        yield su

    case App(inst, pats) =>
      val ec = classes(id.find)

      for (
        EApp(`inst`, args) <- ec.nodes; // monomorphic only
        su <- ematch(pats, args, su)
      ) yield {
        su
      }
  }

  def ematch(
      pats: List[Expr],
      ids: List[EId],
      su0: Map[Var, EId]
  ): Set[Map[Var, EId]] = (pats, ids) match {
    case (Nil, Nil) =>
      Set(su0)
    case (pat :: pats, id :: ids) =>
      for (
        su1 <- ematch(pat, id, su0);
        su2 <- ematch(pats, ids, su1)
      )
        yield su2
  }

  def eunify(
      nd1: ENode,
      nd2: ENode,
      su: Map[Var, ENode] = Map()
  ): Set[Map[Var, ENode]] = (nd1, nd2) match {
    case _ if nd1 == nd2 =>
      Set(Map()) // one trivial solution
    case (EVar(x1), _) if su contains x1 =>
      eunify(su(x1), nd2, su)
    case (nd1 @ EVar(x1), _) /* if !(nd1 in nd2) */ =>
      Set(su + (x1 -> nd2))
    case (_: EVar, _) =>
      Set() // recursive
    case (_, _: EVar) =>
      eunify(nd2, nd1, su)
    case (EApp(inst1, args1), EApp(inst2, args2)) if inst1 == inst2 =>
      eunify_classes(args1, args2, su)
    case _ =>
      Set()
  }

  def eunify(
      id1: EId,
      nd2: ENode,
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = {
    val ec1 = classes(id1.find)
    for (
      nd1 <- ec1.nodes;
      su1 <- eunify(nd1, nd2, su0)
    )
      yield su1
  }

  def eunify(
      id1: EId,
      id2: EId,
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = {
    val ec1 = classes(id1.find)
    val ec2 = classes(id2.find)
    for (
      nd1 <- ec1.nodes;
      nd2 <- ec2.nodes;
      su1 <- eunify(nd1, nd2, su0)
    )
      yield su1
  }

  def eunify_classes(
      ids1: List[EId],
      ids2: List[EId],
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = (ids1, ids2) match {
    case (Nil, Nil) =>
      Set(su0)
    case (id1 :: ids1, id2 :: ids2) =>
      for (
        su1 <- eunify(id1, id2, su0);
        su2 <- eunify_classes(ids2, ids2, su1)
      )
        yield su2
  }

  def eunify(
      nds1: List[ENode],
      nds2: List[ENode],
      su0: Map[Var, ENode]
  ): Set[Map[Var, ENode]] = (nds1, nds2) match {
    case (Nil, Nil) =>
      Set(su0)
    case (nd1 :: nds1, nd2 :: nds2) =>
      for (
        su1 <- eunify(nd1, nd2, su0);
        su2 <- eunify(nds2, nds2, su1)
      )
        yield su2
  }

  def ematch(pat: Expr): List[(Map[Var, EId], EId)] = {
    for (
      (nd, id) <- hash.toList;
      su <- ematch(pat, id)
    )
      yield (su, id)
  }

  def esubst(id: EId, ty: Map[Param, Type], su: Map[Var, EId]): EId = {
    val ec = classes(id.find)
    val nodes = ec.nodes map (esubst(_, ty, su))
    val id0 = nodes.head
    for (idk <- nodes)
      merge(id0, idk)
    id0
  }

  def esubst(nd: ENode, ty: Map[Param, Type], su: Map[Var, EId]): EId =
    nd match {
      case EVar(x) if su contains x =>
        su(x)
      case _: EVar | _: ELit =>
        add(nd)
      case EApp(inst, args) =>
        val inst_ = inst subst ty
        val args_ = args map (esubst(_, ty, su))
        add(EApp(inst_, args_))
    }

  def ematches(rules: List[Rule]) = {
    for (
      rule @ Rule(lhs, rhs, True, avoid) <- rules;
      (su, lhs_) <- ematch(lhs)
    ) yield {
      val bad = avoid exists { case (a, b) =>
        val a_ = subst(a, su)
        val b_ = add(b)
        a_ == b_
      }

      val rhs_ = subst(rhs, su)
      if (debug) {
        println("applying rule " + rule)
        println("substituting " + rhs + " by " + su)
        println("rewriting " + lhs_ + " ~> " + rhs_)
      }

      (bad, rule, su, lhs_ -> rhs_)
    }
  }

  def subst(expr: Expr, su: Map[Var, EId]): EId = expr match {
    case x: Var if su contains x =>
      su(x)
    case x: Var =>
      add(EVar(x))
    case Lit(any, typ) =>
      add(ELit(any, typ))
    case App(inst, args) =>
      add(EApp(inst, args map (subst(_, su))))
    case _ =>
      cuvee.error("cannot add to e-graph: " + expr + " (via subst)")
  }

  def rewrite(rules: List[Rule]) = {
    var done = true

    // XXX: forall is non strict!!
    for ((bad, rule, su, (lhs, rhs)) <- ematches(rules)) {
      if (bad) {
        if (debug)
          println("avoiding bad match " + lhs.find + " and " + rhs.find)
      } else {
        val same = lhs.find == rhs.find
        if (!same) {
          merge(lhs, rhs)
          done = false
        } else {
          if (debug)
            println("not merging " + lhs.find + " and " + rhs.find)
        }
      }
    }

    rebuild()

    done
  }

  final def saturate(rules: List[Rule]) {
    while (!rewrite(rules)) {}
  }
}

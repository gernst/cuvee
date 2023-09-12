package cuvee.egraph

import scala.collection.mutable

import cuvee.pure._

class EGraph {
  val hash = mutable.Map[ENode, EClass]()
  val todo = mutable.Set[EClass]()
  val classes = mutable.Set[EClass]()

  var debug = false

  def invariants() {
    val nds =
      for (ec <- classes; nd <- ec.nodes)
        yield nd

    assert(hash.keySet == nds)

    for (ec <- classes; nd <- ec.nodes) {
      assert(nd.canon == nd, "not canonical: " + nd + " in " + ec)
      assert(hash(nd.canon).find == ec.find)
    }

    for ((nd, ec) <- hash) {
      assert(hash(nd.canon).find == ec.find)
    }
  }

  object EClass extends cuvee.util.Counter

  class EClass(var parents: Map[ENode, EClass], var nodes: Set[ENode]) {
    require(nodes.nonEmpty, "an e-class must be nonempty")
    val id = EClass.next

    override def toString = {
      // assert(id == find.id)
      if (nodes.size == 1) {
        val nd = nodes.head
        nd.toString
      } else {
        "eclass$" + id + "$" + find.id
      }
    }

    def this(nd: ENode) = this(Map(), Set(nd))

    var repr: EClass = this

    def find: EClass = {
      if (repr != this)
        repr = repr.find // compaction
      repr
    }

    def union(that: EClass) {
      that.repr = this // make this the representant
      this.parents ++= that.parents
      this.nodes ++= that.nodes
    }
  }

  sealed trait ENode {
    def args: List[EClass]
    def canon: ENode
  }

  case class EVar(x: Var) extends ENode {
    def args = Nil
    def canon = this
    override def toString = x.toString
  }

  case class ELit(any: Any, typ: Type) extends ENode {
    def args = Nil
    def canon = this
    override def toString = any.toString
  }

  case class EApp(inst: Inst, var args: List[EClass]) extends ENode {
    def canon = {
      args = args map (_.find)
      this
    }

    override def toString = this match {
      case EApp(inst, Nil) =>
        inst.toString
      case _ =>
        inst + args.mkString("(", ", ", ")")
    }
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
      val ec = new EClass(nd)
      classes += ec

      for (arg <- nd.args)
        arg.parents += nd -> ec

      assert(ec == ec.find)
      hash(nd) = ec

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

      todo.clear()

      for (id <- now)
        repair(id) // may add some more todos
    }

    invariants()
  }

  def repair(ec: EClass) {
    if (debug)
      println("repair " + ec)

    assert(ec.find == ec)

    for ((pnd, pec) <- ec.parents) {
      hash -= pnd
      hash(pnd.canon) = pec.find
    }

    var parents: Map[ENode, EClass] = Map()

    for ((pnd, pec) <- ec.parents) {
      assert(pnd.canon == pnd)
      // val pnd = pnd_.canon
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
      Set(su + (x -> ec))

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

  def ematch(pat: Expr): List[(Map[Var, EClass], EClass)] = {
    for (
      (nd, id) <- hash.toList;
      su <- ematch(pat, id)
    )
      yield (su, id)
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
      (bad, rule, su, lhs_ -> rhs_)
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

  def rewrite(rules: List[Rule]) = {
    var done = true

    for ((bad, rule, su, (lhs, rhs)) <- ematches(rules)) {
      if (!bad) {
        val same = lhs.find == rhs.find
        if (!same) {
          merge(lhs, rhs)
          done = false
        }
      }
    }

    rebuild()

    done
  }

  def saturate(rules: List[Rule]) {
    while (!rewrite(rules)) {}
  }
}

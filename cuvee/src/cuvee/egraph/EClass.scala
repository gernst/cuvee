package cuvee.egraph

import cuvee.util.Fix
import cuvee.pure._

object EClass extends cuvee.util.Counter

class EClass(
    val egraph: EGraph,
    var parents: Map[ENode, EClass],
    var canon: ENode,
    var nodes: Set[ENode]
) {
  require(nodes.nonEmpty, "an e-class must be nonempty")
  val id = EClass.next

  def exprs = egraph.extract(this)
  def isTrue = nodes exists (_.isTrue)

  def this(egraph: EGraph) = this(egraph, Map(), null, Set())
  def this(egraph: EGraph, nd: ENode) = this(egraph, Map(), nd, Set(nd))

  var repr: EClass = this

  def find: EClass = {
    if (repr != this)
      repr = repr.find // compaction
    repr
  }

  def union(that: EClass) {
    assert(this.egraph == that.egraph)
    that.repr = this // make this the representant
    this.parents ++= that.parents
    this.nodes ++= that.nodes
  }

  def replace(f: Fun, g: Fun) {
    parents =
      for ((pnd, pec) <- parents)
        yield (pnd.replace(f, g), pec)

    nodes =
      for (nd <- nodes)
        yield nd.replace(f, g)
  }

  def transfer(map: Map[EClass, EClass]) = {
    val that = map(this)

    that.canon = canon.transfer(map)

    that.parents =
      for ((pnd, pec) <- parents)
        yield pnd.transfer(map) -> map(pec)

    that.nodes =
      for (nd <- nodes)
        yield nd.transfer(map)

    that
  }

  def free = {
    val (_, _, res) = Fix.digraph[EClass, Var](
      this,
      _.nodes collect { case EVar(x) => x },
      _.nodes flatMap (_.args)
    )
    res(this)
  }

  def funs = {
    val (_, _, res) = Fix.digraph[EClass, Fun](
      this,
      _.nodes collect { case EApp(inst, _) => inst.fun },
      _.nodes flatMap (_.args)
    )
    res(this)
  }

  override def toString = {
    // assert(id == find.id)
    if (nodes.size == 1) {
      val nd = nodes.head
      nd.toString
    } else {
      "eclass$" + id + "$" + find.id
    }
  }
}

package cuvee.egraph

import cuvee.util.Fix
import cuvee.pure._

object EClass extends cuvee.util.Counter

class EClass(
    var parents: Map[ENode, EClass],
    var canon: ENode,
    var nodes: Set[ENode]
) {
  require(nodes.nonEmpty, "an e-class must be nonempty")
  val id = EClass.next

  def isTrue = nodes exists (_.isTrue)

  def this() = this(Map(), null, Set())
  def this(nd: ENode) = this(Map(), nd, Set(nd))

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

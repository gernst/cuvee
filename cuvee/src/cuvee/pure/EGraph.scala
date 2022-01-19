package cuvee.pure

import scala.collection.mutable

class EGraph {
  sealed trait ENode {
    def args: List[EClass]
    def canon: ENode
  }

  case class EVar(x: Var) extends ENode {
    def args = Nil
    def canon = this
  }

  case class EApp(fun: Fun, inst: Inst, args: List[EClass]) extends ENode {
    def canon = EApp(fun, inst, args map (_.find))
  }

  class EClass(var parents: Map[ENode, EClass], var nodes: Set[ENode]) {
    var repr: EClass = this

    def find: EClass = {
      if (repr != this)
        repr = repr.find
      repr
    }

    def union(that: EClass): EClass = {
      repr = that
      repr
    }

    def ematch(
        pat: Expr,
        sus: Set[Map[Var, EClass]]
    ): Set[Map[Var, EClass]] = pat match {
      case x: Var =>
        sus collect {
          case su if !(su contains x) =>
            su + (x -> this)
          case su if (su contains x) && su(x).find == find =>
            su
        }

      case App(fun, inst, pats) =>
        for (
          EApp(`fun`, _, args) <- nodes; // do we have to check?
          su <- {
            (pats zip args).foldLeft(sus) { case (sus, (pat, ec)) =>
              ec ematch (pat, sus)
            }
          }
        )
          yield su
    }
  }

  val hash = mutable.Map[ENode, EClass]()
  val todo = mutable.Set[EClass]()

  def add(expr: Expr): EClass = expr match {
    case x: Var =>
      add(EVar(x))
    case App(fun, inst, args) =>
      add(EApp(fun, inst, args map add))
  }

  def merge(lhs: Expr, rhs: Expr): EClass = {
    merge(add(lhs), add(rhs))
  }

  def add(nd_ : ENode): EClass = {
    val nd = nd_.canon

    if (hash contains nd) {
      hash(nd)
    } else {
      val ec = new EClass(Map(), Set(nd))
      for (arg <- nd.args)
        arg.parents += nd -> ec
      hash(nd) = ec
      ec
    }
  }

  def merge(ec1: EClass, ec2: EClass): EClass = {
    if (ec1.find == ec2.find) {
      ec1.find // compacted now
    } else {
      val ec = ec1 union ec2
      todo += ec
      ec
    }
  }

  def rebuild() {
    while (todo.nonEmpty) {
      val now = todo map (_.find)
      todo.clear()

      for (ec <- now)
        repair(ec) // may add some more todos
    }
  }

  def repair(ec: EClass) {
    for ((pnd, pec) <- ec.parents) {
      hash -= pnd
      hash(pnd.canon) = pec.find
    }

    var parents: Map[ENode, EClass] = Map()

    for ((pnd_, pec) <- ec.parents) {
      val pnd = pnd_.canon
      if (parents contains pnd)
        merge(pec, parents(pnd))
      parents += pnd -> pec.find
    }

    ec.parents = parents
  }
}

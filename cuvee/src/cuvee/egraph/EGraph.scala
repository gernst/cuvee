package cuvee.egraph

import scala.collection.mutable

import cuvee.pure._
import scala.annotation.tailrec

class EGraph {
  var debug = false

  val hash = mutable.Map[ENode, EClass]()
  val todo = mutable.Set[EClass]()
  def classes = hash.values.toSet filter (_.nonEmpty)

  def invariant() {
    
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

  case class EApp(inst: Inst, args: List[EClass]) extends ENode {
    def canon = EApp(inst, args map (_.find))

    override def toString = this match {
      case EApp(inst, Nil) =>
        inst.toString
      case _ =>
        inst + args.mkString("(", ", ", ")")
    }
  }

  class EClass(var parents: Map[ENode, EClass], var nodes: Set[ENode]) {
    var repr: EClass = this

    def isEmpty = nodes.isEmpty
    def nonEmpty = nodes.nonEmpty

    def subst(ty: Map[Param, Type], su: Map[Var, EClass]) = {
      val nodes_ = nodes map (esubst(_, ty, su))
      ???
    }

    override def toString = if (repr == this) {
      if (nodes.size == 1) {
        nodes.head.toString
      } else {
        nodes.mkString("{ ", ", ", " }")
      }
    } else {
      "..."
    }

    def exprs: Set[Expr] = nodes flatMap {
      case EVar(x) =>
        Set(x)

      case ELit(any, typ) =>
        Set(Lit(any, typ))

      case EApp(inst, args) =>
        def collect(args: List[EClass]): Set[List[Expr]] = args match {
          case Nil =>
            Set(Nil)
          case arg :: rest =>
            for (
              arg_ <- arg.exprs;
              rest_ <- collect(rest)
            )
              yield arg_ :: rest_
        }

        for (args_ <- collect(args))
          yield App(inst, args_): Expr
    }

    def find: EClass = {
      if (repr != this)
        repr = repr.find
      repr
    }

    def union(that: EClass): EClass = {
      require(
        this.repr == this && that.repr == that,
        "cannot union non canonical classes"
      )

      if (debug)
        println("merging " + that + " into " + this)

      that.repr = this

      // Note: We cannot get rid of the old classes just like that:
      //       the nodes still refer to them in that hash map,
      //       and we would have to update the reference there,
      //       but *also* and recursively all occurrences inside EApp args.
      //       Therefore, we can just keep that class around
      //       (perhaps we could empty its list of nodes)

      parents ++= that.parents
      nodes ++= that.nodes

      that.clear()

      this
    }

    def clear() {
      nodes = Set()
      parents = Map()
    }

    def ematch(
        pat: Expr,
        sus: Set[Map[Var, EClass]] = Set(Map())
    ): Set[Map[Var, EClass]] = pat match {
      case x: Var =>
        sus collect {
          case su if !(su contains x) =>
            su + (x -> this)
          case su if (su contains x) && su(x).find == find =>
            su
        }

      case Lit(any, typ) =>
        for (
          ELit(`any`, `typ`) <- nodes;
          su <- sus
        )
          yield su

      case App(inst, pats) =>
        for (
          EApp(`inst`, args) <- nodes; // do we have to check?
          su <- {
            (pats zip args).foldLeft(sus) { case (sus, (pat, ec)) =>
              ec ematch (pat, sus)
            }
          }
        ) yield {
          su
        }
    }
  }

  def eunify(
      pat: Expr,
      sus: Set[Map[Var, EClass]] = Set(Map())
  ): Set[Map[Var, EClass]] = pat match {
    case _ =>
      ???
  }

  def esubst(nd: ENode, ty: Map[Param, Type], su: Map[Var, EClass]): EClass =
    nd match {
      case EVar(x) if su contains x =>
        su(x)
      case _: EVar | _: ELit =>
        add(nd)
      case EApp(inst, args) =>
        val inst_ = inst subst ty
        ???
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

  def subst(expr: Expr, su: Map[Var, EClass]): EClass = expr match {
    case x: Var if su contains x =>
      su(x)
    case x: Var =>
      add(EVar(x))
    case Lit(any, typ) =>
      add(ELit(any, typ))
    case App(inst, args) =>
      add(EApp(inst, subst(args, su)))
    case _ =>
      cuvee.error("cannot add to e-graph: " + expr + " (via subst)")
  }

  def subst(exprs: List[Expr], su: Map[Var, EClass]): List[EClass] = {
    for (expr <- exprs)
      yield subst(expr, su)
  }

  def merge(lhs: Expr, rhs: Expr): EClass = {
    merge(add(lhs), add(rhs))
  }

  def add(nd_ : ENode): EClass = {
    val nd = nd_.canon

    if (hash contains nd) {
      if (debug)
        println("known " + nd)
      hash(nd)
    } else {
      val ec = new EClass(Map(), Set(nd))
      for (arg <- nd.args)
        arg.parents += nd -> ec
      hash(nd) = ec

      if (debug)
        println("new class " + ec)

      ec
    }
  }

  def merge(ec1: EClass, ec2: EClass): EClass = {
    if (ec1.find == ec2.find) {
      ec1.find // compacted now
    } else {
      val ec = ec1.find union ec2.find
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
      if (parents contains pnd) // wrong! should refer to new_parents
        merge(pec, parents(pnd))
      parents += pnd -> pec.find
    }

    ec.parents = parents
  }

  def ematch(pat: Expr) = {
    for (
      (nd, lhs) <- hash;
      su <- lhs ematch pat
    )
      yield (su, lhs)
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

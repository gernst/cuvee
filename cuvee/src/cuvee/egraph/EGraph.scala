package cuvee.egraph

import scala.collection.mutable

import cuvee.pure._
import scala.annotation.tailrec

class EGraph {
  var debug = false

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

    def id =
      hashCode

    // def toString(nd: ENode, known: Set[EClass]): String = nd match {
    //   case _: EVar | _: ELit =>
    //     nd.toString
    //   case EApp(inst, Nil) =>
    //     inst.toString
    //   case EApp(inst, args) =>
    //     val known_ = known ++ args
    //     val strings = args map (_ toString known_)
    //     inst + strings.mkString("(", ", ", ")")
    // }

    // def toString(known: Set[EClass]): String = if (known contains this) {
    //   "..."
    // } else {
    //   val strings = nodes map (toString(_, known))
    //   if (strings.size == 1)
    //     strings.head
    //   else
    //     strings.mkString("{ ", ", ", " }")
    // }

    // override def toString: String =
    //   toString(Set())
    override def toString = if (nodes.size == 1) {
      nodes.head.toString
    } else {
      nodes.mkString("{ ", ", ", " }")
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

      hash filterInPlace { case (_, ec) =>
        that != ec
      }

      parents ++= that.parents
      nodes ++= that.nodes

      this
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

  def classes = hash.values.toSet
  val hash = mutable.Map[ENode, EClass]()
  val todo = mutable.Set[EClass]()

  def add(expr: Expr): EClass = expr match {
    case x: Var =>
      add(EVar(x))
    case Lit(any, typ) =>
      add(ELit(any, typ))
    case App(inst, args) =>
      add(EApp(inst, args map add))
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
      if (parents contains pnd)
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

      println("applying rule " + rule)
      println("substituting " + rhs + " by " + su)
      val rhs_ = subst(rhs, su)
      println("rewriting " + lhs_ + " ~> " + rhs_)
      println()
      (bad, rule, su, lhs_ -> rhs_)
    }
  }

  def rewrite(rules: List[Rule]) = {
    var done = true

    // XXX: forall is non strict!!
    for ((bad, rule, su, (lhs, rhs)) <- ematches(rules)) {
      if (bad) {
        println("avoiding bad match " + lhs.find + " and " + rhs.find)
      } else {
        val same = lhs.find == rhs.find
        if (!same) {
          merge(lhs, rhs)
          done = false
        } else {
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

package cuvee.pure

import cuvee.StringOps
import cuvee.error
import cuvee.util
import cuvee.util.Name
import cuvee.util.Alpha

sealed trait Type extends Type.term with util.Syntax {}

case class Datatype(params: List[Param], constrs: List[(Fun, List[Fun])]) extends util.Syntax

object Type extends Alpha[Type, Param] {
  case class CannotUnify(reason: String) extends Exception {
    override def toString = "cannot unify: " + reason
  }

  case class CannotBind(typ1: Type, typ2: Type, su: Map[Param, Type]) extends Exception {
    override def toString = "cannot bind: " + typ1 + " to " + typ2 + " using " + su
  }

  def prune(su: Map[Param, Type]): Map[Param, Type] = {
    for ((p, t) <- su)
      yield (p, prune(t, su))
  }

  def prune(typ: Type, su: Map[Param, Type]): Type = typ match {
    case p: Param if su contains p =>
      prune(su(p), su)
    case p: Param =>
      p
    case Sort(con, args) =>
      Sort(con, args map (prune(_, su)))
  }

  def unify(typ1: Type, typ2: Type, su: Map[Param, Type] = Map()): Map[Param, Type] = {
    (typ1, typ2) match {
      case _ if typ1 == typ2 =>
        su
      case (p1: Param, _) if su contains p1 =>
        unify(su(p1), typ2, su)
      case (_, p2: Param) if su contains p2 =>
        unify(typ1, su(p2), su)
      case (p1: Param, _) if p1 in typ2 =>
        cuvee.undefined
        throw CannotUnify("recursive unification, " + p1 + " in " + typ2)
      case (p1: Param, _) =>
        su + (p1 -> typ2)
      case (_, p2: Param) =>
        unify(p2, typ1, su)
      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        unify(args1, args2, su)
      case _ =>
        throw CannotUnify("cannot unify incompatible " + typ1 + " and " + typ2)
    }
  }

  def unify(
      types1: List[Type],
      types2: List[Type],
      su: Map[Param, Type]
  ): Map[Param, Type] = {
    (types1, types2) match {
      case (Nil, Nil) =>
        su
      case (typ1 :: types1, typ2 :: types2) =>
        unify(types1, types2, unify(typ1, typ2, su))
      case _ =>
        throw CannotUnify("cannot unify incompatible " + types1 + " and " + types2)
    }
  }

  def unify(
      types1: List[Type],
      res1: Type,
      types2: List[Type],
      res2: Type,
      su: Map[Param, Type]
  ): Map[Param, Type] = {
    unify(types1, types2, unify(res1, res2, su))
  }

  def bind(
      typ1: Type,
      typ2: Type,
      su: Map[Param, Type] = Map()
  ): Map[Param, Type] = {
    (typ1, typ2) match {
      // DO NOT DO THIS!
      // typ1 and typ2 have disjoint set of variables
      // case _ if typ1 == typ2 =>
      //   su
      case (p: Param, _) if su contains p =>
        if (su(p) != typ2)
          throw CannotBind(typ1, typ2, su)
        su
      case (p1: Param, _) =>
        su + (p1 -> typ2)
      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        binds(args1, args2, su)
      case _ =>
        throw CannotBind(typ1, typ2, su)
    }
  }

  def binds(
      types1: List[Type],
      res1: Type,
      types2: List[Type],
      res2: Type,
      su: Map[Param, Type]
  ): Map[Param, Type] = {
    binds(types1, types2, bind(res1, res2, su))
  }

  def binds(
      types1: List[Type],
      types2: List[Type],
      su: Map[Param, Type] = Map()
  ): Map[Param, Type] = {
    (types1, types2) match {
      case (Nil, Nil) =>
        su
      case (typ1 :: types1, typ2 :: types2) =>
        binds(types1, types2, bind(typ1, typ2, su))
    }
  }

  // def bind(
  //     inst1: Inst,
  //     inst2: Inst,
  //     su: Map[Param, Type]
  // ): Map[Param, Type] = {
  //   (inst1, inst2) match {
  //     case (Inst(args1, res1), Inst(args2, res2)) =>
  //       binds(args1, args2, bind(res1, res2, su))
  //   }
  // }
}

class ParamList(params: List[Param]) extends Type.xs(params) {
  def names = params map { case Param(name) => name }
  def asContext = params map { case p @ Param(name) => name -> p }
}

class TypeList(types: List[Type]) extends Type.terms(types)

case class Param(name: Name) extends Type with Type.x {
  def fresh(index: Int) =
    Param(name withIndex index)

  def in(typ: Type): Boolean = {
    typ match {
      case that: Param =>
        return this == that
      case Sort(_, args) =>
        args exists (this in _)
    }
  }

  def in(types: List[Type]): Boolean = {
    types exists (this in _)
  }

  override def toString = name.toString
}

object Param {
  val from: (Name => Param) =
    name => Param(name)

  def fresh(name: Name) = {
    Param(name withIndex Type.nextIndex)
  }
}

case class Con(name: Name, arity: Int) {
  override def toString = name.toString + "/" + arity
}

object Con {
  val bool = Con("Bool", 0)
  val int = Con("Int", 0)
  val real = Con("Real", 0)
  val list = Con("List", 1)
  val array = Con("Array", 2)
}

case class Sort(con: Con, args: List[Type]) extends Type {
  def free = args.free
  def rename(re: Map[Param, Param]) =
    Sort(con, args rename re)
  def subst(su: Map[Param, Type]) =
    Sort(con, args subst su)

  override def toString = this match {
    case Sort(con, Nil) =>
      con.name.toString
    case Sort(Con.array, List(a, b)) =>
      "[" + a + "]" + b
    case _ =>
      con.name.toString + args.mkString("<", ", ", ">")
  }
}

object Sort extends ((Con, List[Type]) => Sort) {
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)

  def list(a: Type) =
    Sort(Con.list, List(a))

  val array: ((Type, Type) => Type) =
    (a: Type, b: Type) => Sort(Con.array, List(a, b))
}

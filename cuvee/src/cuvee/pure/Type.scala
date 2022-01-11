package cuvee.pure

import cuvee.StringOps
import cuvee.fail
import cuvee.sexpr

sealed trait Type extends Type.term with sexpr.Syntax {}

case class Datatype(params: List[Param], constrs: List[(Fun, List[Fun])])
    extends sexpr.Syntax {
  def sexpr = if (params.isEmpty)
    List(???)
  else
    List("par", params, ???)
}

object Type extends Alpha[Type, Param] {
  def unify(typ1: Type, typ2: Type, su: Map[Param, Type]): Map[Param, Type] = {
    (typ1, typ2) match {
      case _ if typ1 == typ2 =>
        su
      case (p1: Param, _) if su contains p1 =>
        unify(su(p1), typ2, su)
      case (_, p2: Param) if su contains p2 =>
        unify(typ1, su(p2), su)
      case (p1: Param, _) =>
        require(!(p1 in typ2), "recursive unification, " + p1 + " in " + typ2)
        su + (p1 -> typ2)
      case (_, p2: Param) =>
        unify(p2, typ1, su)
      case (Prod(args1), Prod(args2)) =>
        unify(args1, args2, su)
      case (Sum(args1), Sum(args2)) =>
        unify(args1, args2, su)
      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        unify(args1, args2, su)
      case _ =>
        fail("cannot unify " + typ1 + " and " + typ2)
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
        cuvee.fail("cannot unify " + types1 + " and " + types2)
    }
  }
}

class ParamList(params: List[Param]) extends Type.xs(params) {
  def names = params map { case Param(name, None) => name }
}

class TypeList(types: List[Type]) extends Type.terms(types)

case class Param(name: String, index: Option[Int] = None)
    extends Type
    with Type.x {
  def fresh(index: Int) =
    Param(name, Some(index))

  def in(typ: Type): Boolean = {
    typ match {
      case that: Param =>
        return this == that
      case Sort(_, args) =>
        args exists (this in _)
      case Prod(args) =>
        args exists (this in _)
      case Sum(args) =>
        args exists (this in _)
    }
  }

  def sexpr = name ~~ index
  override def toString = name __ index
}

case class Con(name: String, arity: Int) {
  override def toString = name + "/" + arity
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

  def sexpr =
    if (args.isEmpty)
      con.name
    else
      con.name :: args

  override def toString =
    if (args.isEmpty)
      con.name
    else
      con.name + args.mkString("[", ", ", "]")
}

case class Prod(args: List[Type]) extends Type {
  def free = args.free

  def rename(re: Map[Param, Param]) =
    Prod(args rename re)

  def subst(su: Map[Param, Type]) =
    Prod(args subst su)

  def sexpr = ???
  override def toString =
    args.mkString("(", " * ", ")")
}

case class Sum(args: List[Type]) extends Type {
  def free = args.free

  def rename(re: Map[Param, Param]) =
    Sum(args rename re)

  def subst(su: Map[Param, Type]) =
    Sum(args subst su)

  def sexpr = ???
  override def toString =
    args.mkString("(", " + ", ")")
}

object Sort {
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)

  def list(a: Type) = Sort(Con.list, List(a))
  def array(a: Type, b: Type) = Sort(Con.array, List(a, b))

  def prod(as: List[Type]) =
    as match {
      case List(a) => a
      case _       => Prod(as)
    }

  def sum(as: List[Type]) =
    as match {
      case Nil => fail("cannot form empty sum (SMT-LIB types are inhabitated)")
      case List(a) => a
      case _       => Sum(as)
    }
}

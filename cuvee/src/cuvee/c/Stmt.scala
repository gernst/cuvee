package cuvee.c

case class Dims(ptr: Boolean, bounds: List[Expr]) {
  def this(ptr: Boolean, bounds: Array[Expr]) = this(ptr, bounds.toList)
}

object Dims {
  val empty = Dims(false, Nil)
}

case class ParamSpec(typ: Type, name: Option[String], dims: Dims) {
  def this(typ: Type, dims: Dims) = this(typ, None, dims)
  def this(typ: Type, name: String) = this(typ, Some(name), Dims.empty)
  def this(typ: Type, name: String, dims: Dims) = this(typ, Some(name), dims)
}

case class VarSpec(ptrs: Int, name: String, dims: Dims, init: Option[Expr]) {
  def this(ptrs: Int, name: String, dims: Dims) = this(ptrs, name, dims, None)
  def this(ptrs: Int, name: String, dims: Dims, init: Expr) = this(ptrs, name, dims, Some(init))
}

case class FieldSpec(ptrs: Int, name: String, dims: Dims) {
  def this(ptrs: Int, name: String) = this(ptrs, name, Dims.empty)
}

trait MemberSpecs
case class FieldsSpec(typ: Type, fields: Array[FieldSpec]) extends MemberSpecs
case class FlatUnionSpec(fields: Array[MemberSpecs]) extends MemberSpecs

object Parsing {
  def unescape0(xs: List[Char]): List[Char] = {
    xs match {
      case '\"' :: Nil       => Nil
      case '\\' :: x :: rest => x :: unescape0(rest)
      case x :: rest         => x :: unescape0(rest)
      case _                 => cuvee.error("nonterminated string: " + xs)
    }
  }

  def unescape(xs: List[Char]): List[Char] = {
    xs match {
      case '\"' :: rest => unescape0(rest)
      case _            => cuvee.error("nonterminated string")
    }
  }

  def ch(s: String): Char = {
    s.toList match {
      case List('\'', '\\', x, '\'') => x
      case List('\'', x, '\'')       => x
      case _                         => cuvee.error("invalid character: " + s)
    }
  }

  def str(s: String): String = {
    val xs = unescape(s.toList)
    xs.mkString
  }

  def wrap(typ: Type, n: Int): Type = {
    if (n <= 0) typ
    else wrap(PtrType(typ), n - 1)
  }

  def params(specs: Array[ParamSpec]) =
    specs match {
      case Array(ParamSpec(Type._void, None, Dims.empty)) =>
        Array[Type]()
      case _ =>
        for (spec <- specs)
          yield {
            val ParamSpec(typ, _, dims) = spec
            typ withDims dims
          }
    }

  def formals(specs: Array[ParamSpec]) =
    specs match {
      case Array(ParamSpec(Type._void, None, Dims.empty)) =>
        Array[Formal]()
      case _ =>
        for ((spec, i) <- specs.zipWithIndex)
          yield spec match {
            case ParamSpec(typ, Some(name), dims) =>
              Formal(typ withDims dims, name)
            case ParamSpec(typ, None, dims) =>
              Formal(typ withDims dims, "param" + i)
          }
    }

  def flatten(group: MemberSpecs): Array[Field] = {
    group match {
      case f: FieldsSpec    => fields(f)
      case u: FlatUnionSpec => flatunion(u)
    }
  }

  def members(groups: Array[MemberSpecs]) = {
    for (
      group <- groups;
      field <- flatten(group)
    )
      yield field
  }

  def fields(group: FieldsSpec) = {
    for (field <- group.fields)
      yield {
        val FieldSpec(ptrs, name, dims) = field
        Field(wrap(group.typ withDims dims, ptrs), name)
      }
  }

  def flatunion(group: FlatUnionSpec) = {
    for (
      stuff <- group.fields;
      field <- flatten(stuff)
    ) yield field
  }

  def vars(typ: Type, group: Array[VarSpec]) = {
    for (vars <- group)
      yield {
        val VarSpec(ptrs, name, dims, init) = vars
        VarDef(Formal(wrap(typ withDims dims, ptrs), name), init)
      }
  }
}

sealed trait Stmt

case class Block(stmts: List[Stmt]) extends Stmt {
  def this(stmts: Array[Stmt]) = this(stmts.toList)
}

case class Group(stmts: List[Stmt]) extends Stmt {
  def this(stmts: Array[Stmt]) = this(stmts.toList)
  def this(first: Stmt, second: Stmt) = this(List(first, second))
}

case class Atomic(expr: Option[Expr]) extends Stmt {
  def this(expr: Expr) = this(Some(expr))
}

object Atomic {
  val none = Atomic(None)
  // def assume(expr: Expr) = Atomic(Some(__VERIFIER.assume(expr)))
}

case class Label(label: String, stmt: Stmt) extends Stmt

case class Case(const: Any, stmt: Stmt) extends Stmt

case class Goto(label: String) extends Stmt

case object Break extends Stmt {
  def self = this
}

case object Continue extends Stmt {
  def self = this
}

case class Return(expr: Option[Expr]) extends Stmt {
  def this(expr: Expr) = this(Some(expr))
}

object Return {
  val none = Return(None)
}

case class If(test: Expr, left: Stmt, right: Stmt) extends Stmt {
  def this(test: Expr, left: Stmt) = this(test, left, Block(Nil))
}

case class While(test: Expr, body: Stmt) extends Stmt

case class DoWhile(body: Stmt, test: Expr) extends Stmt

case class For(vars: List[VarDef], init: List[Expr], test: List[Expr], inc: List[Expr], body: Stmt)
    extends Stmt {

  def this(init: Array[Expr], test: Array[Expr], inc: Array[Expr], body: Stmt) = {
    this(Nil, init.toList, test.toList, inc.toList, body)
  }

  def this(vars: Array[VarDef], test: Array[Expr], inc: Array[Expr], body: Stmt) = {
    this(vars.toList, Nil, test.toList, inc.toList, body)
  }
}

case class TypeDef(typ: Type, name: String) extends Stmt {}

case class StructDef(name: String, fields: List[Field]) extends Stmt {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class UnionDef(name: String, fields: List[Field]) extends Stmt {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class EnumDef(name: Option[String], consts: List[Const]) extends Stmt {
  def this(consts: Array[Const]) = this(None, consts.toList)
  def this(name: String, consts: Array[Const]) = this(Some(name), consts.toList)
}

case class StructDecl(name: String) extends Stmt
case class UnionDecl(name: String) extends Stmt
case class EnumDecl(name: String) extends Stmt

case class Switch(expr: Expr, body: Stmt) extends Stmt {}

case class VarDef(formal: Formal, init: Option[Expr]) extends Stmt {
  def this(formal: Formal) = this(formal, None)
  def this(formal: Formal, init: Expr) = this(formal, Some(init))
}

case class FunDecl(ret: Type, name: String, types: List[Formal]) extends Stmt {
  def this(ret: Type, name: String) = {
    this(ret, name, Nil)
  }

  def this(ret: Type, name: String, params: Array[Formal]) = {
    this(ret, name, params.toList)
  }
}

case class FunDef(ret: Type, name: String, formals: List[Formal], body: Stmt) extends Stmt {
  def this(ret: Type, name: String, body: Stmt) = {
    this(ret, name, Nil, body)
  }

  def this(ret: Type, name: String, formals: Array[Formal], body: Stmt) = {
    this(ret, name, formals.toList, body)
  }
}

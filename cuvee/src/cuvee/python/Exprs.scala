package cuvee.python

import pythonparse.Ast
import cuvee.pure.Expr
import cuvee.pure.And
import cuvee.pure.Var
import cuvee.pure.Assoc
import cuvee.pure.Sugar
import cuvee.pure.Lit
import cuvee.pure.Forall
import cuvee.pure.Store
import cuvee.pure.Old
import cuvee.pure.Param
import cuvee.pure.Is
import cuvee.pure.Exists
import pythonparse.Ast.unaryop.Invert
import pythonparse.Ast.unaryop.Not
import pythonparse.Ast.unaryop.UAdd
import pythonparse.Ast.unaryop.USub

class Exprs(val sig: Signature) {
  import sig._

  object sugar {
    object Call {
      def unapply(expr: Ast.expr) = expr match {
        case Ast.expr.Call(Ast.expr.Name(Ast.identifier(id), _), args, _, _, _) =>
          Some((id, args))
        case _ =>
          None
      }
    }

    object SelfCall {
      def unapply(expr: Ast.expr) = expr match {
        case Ast.expr.Call(
              Ast.expr.Attribute(Ast.expr.Name(Ast.identifier("self"), _), func, _),
              args,
              _,
              _,
              _
            ) =>
          Some((func, args))
        case _ => None
      }
    }

    object Lambda {
      def unapply(expr: Ast.expr) = expr match {
        case Ast.expr.Lambda(Ast.arguments(formals: Seq[Ast.expr.Name], _, _, _), body) =>
          Some((formals, body))
        case _ =>
          None
      }
    }
  }

  /** Maps pythonparse.Ast.expr to fitting cuvee.pure.Expr
    *
    * This function calls helper functions, which in turn call pymap back. It could be writeen in
    * one function, making the recursion more obvious, but this would come at the cost of
    * readability.
    */
  def pymap(expr: Ast.expr): Expr = expr match {
    case Ast.expr.BoolOp(op, values)     => boolOp(op, values)
    case Ast.expr.UnaryOp(op, operand)   => unaryOp(op, operand)
    case Ast.expr.BinOp(left, op, right) => binaryOp(left, op, right)
    case Ast.expr.Num(n: BigInt)         => pyInt(Lit(n, int))
    case Ast.expr.Name(id, _)            => name(id)

    case Ast.expr.IfExp(test, body, orelse) =>
      pyIte(pymap(test), pymap(body), pymap(orelse))

    case Ast.expr.Compare(
          sugar.Call("type", Seq(arg)),
          Seq(Ast.cmpop.Eq),
          Seq(Ast.expr.Name(pyType, _))
        ) =>
      hasType(pyType, arg)

    case Ast.expr.Compare(
          sugar.Call("type", Seq(arg1)),
          Seq(Ast.cmpop.Eq),
          Seq(sugar.Call("type", Seq(arg2)))
        ) =>
      compareTypes(arg1, arg2)

    case Ast.expr.Compare(
          sugar.Call("type", Seq(arg)),
          Seq(Ast.cmpop.NotEq),
          Seq(Ast.expr.Name(pyType, _))
        ) =>
      pyNot(hasType(pyType, arg))

    case Ast.expr.Compare(
          sugar.Call("type", Seq(arg1)),
          Seq(Ast.cmpop.NotEq),
          Seq(sugar.Call("type", Seq(arg2)))
        ) =>
      pyNot(compareTypes(arg1, arg2))

    case Ast.expr.Compare(left, Seq(op), Seq(right)) =>
      compare(left, op, right)

    case sugar.SelfCall(func, args) =>
      // call(func, args)
      cuvee.error("calls to self._ not supported")

    case Ast.expr.Call(Ast.expr.Name(Ast.identifier(func), _), args, _, _, _) =>
      apply(func, args)

    case Ast.expr.Subscript(values, slice_, _) =>
      slice(values, slice_)

    case Ast.expr.List(elems, _) =>
      pyArray(
        initArray(pyDefaultArray(), elems.toList),
        Lit(elems.length, int)
      )

    case Ast.expr.Attribute(Ast.expr.Name(Ast.identifier("self"), _), attr, _) =>
      Var("self." + attr.name, pyValue)

    case _ => cuvee.error("Unsupported Python expression: " + expr)
  }

  /* The python ast considers land and lor as n-ary operators with n >= 2.
   */
  def boolOp(op: Ast.boolop, values: Seq[Ast.expr]): Expr = op match {
    case Ast.boolop.And => pyAnd(values.toList map pymap)
    case Ast.boolop.Or  => pyOr(values.toList map pymap)
  }

  def unaryOp(op: Ast.unaryop, operand: Ast.expr): Expr = op match {
    case Ast.unaryop.Not  => pyNot(pymap(operand))
    case Ast.unaryop.USub => pyNegate(pymap(operand))
    case _                => cuvee.error("Unsupported unary operation: " + op)
  }

  def compare(
      left: Ast.expr,
      op: Ast.cmpop,
      right: Ast.expr
  ): Expr = op match {
    case Ast.cmpop.Eq    => pyEquals(pymap(left), pymap(right))
    case Ast.cmpop.NotEq => pyNot(pyEquals(pymap(left), pymap(right)))
    case Ast.cmpop.Lt    => pyLessThan(pymap(left), pymap(right))
    case Ast.cmpop.LtE   => pyLessEquals(pymap(left), pymap(right))
    case Ast.cmpop.Gt    => pyGreaterThan(pymap(left), pymap(right))
    case Ast.cmpop.GtE   => pyGreaterEquals(pymap(left), pymap(right))
    case Ast.cmpop.In    => pyIn(pymap(left), pymap(right))
    case Ast.cmpop.NotIn => pyNot(pyIn(pymap(left), pymap(right)))
    case _               => cuvee.error("Unsupported compare operation: " + op)
  }

  /* Assigns static types to pyValues. They are defined in the parsed file
   * via 'requires'. This is necessary since smtlib does not have dynamic types.
   */
  def hasType(pyType: Ast.identifier, expr: Ast.expr): Expr =
    pyType.name match {
      case "int"  => pyBool(Is(pymap(expr), pyInt))
      case "bool" => pyBool(Is(pymap(expr), pyBool))
      case "list" => pyBool(Is(pymap(expr), pyArray))
      case _ =>
        cuvee.error(
          "At the moment only int, bool and list are supported as definable types. Got: " + pyType.name
        )
    }

  /* Type equality implies: It could be any (available) type, which one does not matter.
   * The interesting part is: The types of both arguments are the same.
   */
  def compareTypes(left: Ast.expr, right: Ast.expr): Expr = {
    val types = List(
      pyEquals(pyBool(Is(pymap(left), pyInt)), pyBool(Is(pymap(right), pyInt))),
      pyEquals(pyBool(Is(pymap(left), pyBool)), pyBool(Is(pymap(right), pyBool))),
      pyEquals(pyBool(Is(pymap(left), pyArray)), pyBool(Is(pymap(right), pyArray)))
    )
    pyOr(types)
  }

  def binaryOp(
      left: Ast.expr,
      op: Ast.operator,
      right: Ast.expr
  ): Expr = op match {
    case Ast.operator.Add      => pyAdd(pymap(left), pymap(right))
    case Ast.operator.Sub      => pySub(pymap(left), pymap(right))
    case Ast.operator.Mult     => pyTimes(pymap(left), pymap(right))
    case Ast.operator.FloorDiv => pyFloorDiv(pymap(left), pymap(right))
    case Ast.operator.Mod      => pyMod(pymap(left), pymap(right))
    // case Ast.operator.Pow      => pyPow(pymap(left), pymap(right))
    case _ => cuvee.error("Unsupported binary operation: " + op)
  }

  def slice(values: Ast.expr, slice: Ast.slice) = slice match {
    case Ast.slice.Index(i) =>
      pySelect(pymap(values), pymap(i))
    case Ast.slice.Slice(Some(lower), Some(upper), None) =>
      pySlice(pymap(values), pymap(lower), pymap(upper))
    case Ast.slice.Slice(Some(lower), None, None) =>
      pySlice(pymap(values), pymap(lower), pyInt(pyGetLength(pymap(values))))
    case Ast.slice.Slice(None, Some(upper), None) =>
      pySlice(pymap(values), pyInt(Lit(0, int)), pymap(upper))
    case Ast.slice.Slice(None, None, None) =>
      pySlice(pymap(values), pyInt(Lit(0, int)), pyInt(pyGetLength(pymap(values))))
    case _ =>
      cuvee.error("Currently only default steps for slice are supported.");
  }

  def apply(func: String, args: Seq[Ast.expr]): Expr = (func, args) match {
    case ("old", Seq(arg))        => Old(pymap(arg))
    case ("out", Seq())           => pyResult
    case ("result", Seq())        => pyResult
    case ("len", Seq(arg))        => pyInt(pyGetLength(pymap(arg)))
    case ("imp", Seq(arg1, arg2)) => pyImplies(pymap(arg1), pymap(arg2))

    case ("forall", Seq(sugar.Lambda(formals, body))) =>
      pyBool(
        Forall(
          formals.toList map formal,
          pyIsTrue(pymap(body))
        )
      )

    case ("exists", Seq(sugar.Lambda(formals, body))) =>
      pyBool(
        Exists(
          formals.toList map formal,
          pyIsTrue(pymap(body))
        )
      )
  }

  def formal(name: Ast.expr.Name) =
    Var(name.id.name, pyValue)

  /* Python lists with a static length, defined via requires.
   */
  def initArray(id: Expr, elems: List[Ast.expr], index: Int = 0): Expr =
    elems match {
      case Nil => id
      case head :: next =>
        Store(
          initArray(id, next, index + 1),
          Lit(index, int),
          pymap(head)
        )
    }

  def name(id: Ast.identifier): Expr = id match {
    case Ast.identifier("True")  => pyTrue()
    case Ast.identifier("False") => pyFalse()
    case Ast.identifier("None")  => pyNone()
    case _                       => Var(id.name, pyValue)
  }
}

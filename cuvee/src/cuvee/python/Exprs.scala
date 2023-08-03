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

class Exprs(val sig: Signature) {
  import sig._

  /** Maps pythonparse.Ast.expr to fitting cuvee.pure.Expr
    *
    * This function calls helper functions, which in turn call pymap back. It
    * could be writeen in one function, making the recursion more obvious, but
    * this would come at the cost of readability.
    */
  def pymap(expr: Ast.expr): Expr = expr match {
    case Ast.expr.BoolOp(op, values)     => boolOp(op, values)
    case Ast.expr.UnaryOp(op, operand)   => unaryOp(op, operand)
    case Ast.expr.BinOp(left, op, right) => binaryOp(left, op, right)
    case Ast.expr.IfExp(test, body, orelse) =>
      pyIte(this.pymap(test), this.pymap(body), this.pymap(orelse))
    case Ast.expr.Compare(
          Ast.expr.Call(
            Ast.expr.Name(Ast.identifier("type"), _),
            Seq(expr),
            _,
            _,
            _
          ),
          Seq(Ast.cmpop.Eq),
          Seq(Ast.expr.Name(pyType, _))
        ) =>
      defType(pyType, expr)
    case Ast.expr.Compare(
          Ast.expr.Call(
            Ast.expr.Name(Ast.identifier("type"), _),
            Seq(expr1),
            _,
            _,
            _
          ),
          Seq(Ast.cmpop.Eq),
          Seq(
            Ast.expr.Call(
              Ast.expr.Name(Ast.identifier("type"), _),
              Seq(expr2),
              _,
              _,
              _
            )
          )
        ) =>
      defType(expr1, expr2)
    case Ast.expr.Compare(
          Ast.expr.Call(
            Ast.expr.Name(Ast.identifier("type"), _),
            Seq(expr),
            _,
            _,
            _
          ),
          Seq(Ast.cmpop.NotEq),
          Seq(Ast.expr.Name(pyType, _))
        ) =>
      pyNot(defType(pyType, expr))
    case Ast.expr.Compare(
          Ast.expr.Call(
            Ast.expr.Name(Ast.identifier("type"), _),
            Seq(expr1),
            _,
            _,
            _
          ),
          Seq(Ast.cmpop.NotEq),
          Seq(
            Ast.expr.Call(
              Ast.expr.Name(Ast.identifier("type"), _),
              Seq(expr2),
              _,
              _,
              _
            )
          )
        ) =>
      defType(expr1, expr2)
    case Ast.expr.Compare(left, Seq(op), Seq(comparator)) =>
      comp(left, op, comparator)
    case Ast.expr.Call(
          Ast.expr.Attribute(Ast.expr.Name(Ast.identifier("self"), _), func, _),
          args,
          _,
          _,
          _
        ) =>
      call(func, args)
    case Ast.expr.Call(Ast.expr.Name(func, _), args, _, _, _) =>
      call(func, args)
    case Ast.expr.Subscript(values, slice, _) =>
      this.slice(values, slice)
    case Ast.expr.List(elems, _) =>
      pyArray(
        initArray(pyDefaultArray(), elems.toList),
        Lit(elems.length, int)
      )
    case Ast.expr.Attribute(
          Ast.expr.Name(Ast.identifier("self"), _),
          attr,
          _
        ) =>
      Var("self." + attr.name, value)
    case Ast.expr.Num(n: BigInt) => pyInt(Lit(n, int))
    case Ast.expr.Name(id, _)    => name(id)
    case _                       => cuvee.error("unsupported Python expression: " + expr)
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
    case _                => cuvee.undefined
  }

  def comp(
      left: Ast.expr,
      op: Ast.cmpop,
      comparator: Ast.expr
  ): Expr = op match {
    case Ast.cmpop.Eq    => pyEquals(pymap(left), pymap(comparator))
    case Ast.cmpop.NotEq => pyNot(pyEquals(pymap(left), pymap(comparator)))
    case Ast.cmpop.Lt    => pyLessThan(pymap(left), pymap(comparator))
    case Ast.cmpop.LtE   => pyLessEquals(pymap(left), pymap(comparator))
    case Ast.cmpop.Gt    => pyGreaterThan(pymap(left), pymap(comparator))
    case Ast.cmpop.GtE   => pyGreaterEquals(pymap(left), pymap(comparator))
    case Ast.cmpop.In    => pyIn(pymap(left), pymap(comparator))
    case Ast.cmpop.NotIn => pyNot(pyIn(pymap(left), pymap(comparator)))
    case Ast.cmpop.Is    => cuvee.undefined
    case Ast.cmpop.IsNot => cuvee.undefined
  }

  /* Assigns static types to pyValues. They are defined in the parsed file
   * via 'requires'. This is necessary since smtlib does not have dynamic types.
   */
  def defType(pyType: Ast.identifier, expr: Ast.expr): Expr =
    pyType.name match {
      case "int"  => pyBool(Is(pymap(expr), pyInt))
      case "bool" => pyBool(Is(pymap(expr), pyBool))
      case "list" => pyBool(Is(pymap(expr), pyArray))
    }

  /* Type equality implies: It could be any (available) type, which one does not matter.
   * The interesting part is: The types of both arguments are the same*/
  def defType(left: Ast.expr, right: Ast.expr): Expr = {
    val types = List(
      pyEquals(pyBool(Is(pymap(left), pyInt)), pyBool(Is(pymap(right), pyInt))),
      pyEquals(
        pyBool(Is(pymap(left), pyBool)),
        pyBool(Is(pymap(right), pyBool))
      ),
      pyEquals(
        pyBool(Is(pymap(left), pyArray)),
        pyBool(Is(pymap(right), pyArray))
      )
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
    case _ => cuvee.undefined
  }

  def slice(values: Ast.expr, slice: Ast.slice) = slice match {
    case Ast.slice.Index(i) => pySelect(pymap(values), pymap(i))
    case Ast.slice.Slice(Some(lower), Some(upper), None) =>
      pySlice(pymap(values), pymap(lower), pymap(upper))
    case Ast.slice.Slice(Some(lower), None, None) =>
      pySlice(pymap(values), pymap(lower), pyInt(pyGetLength(pymap(values))))
    case Ast.slice.Slice(None, Some(upper), None) =>
      pySlice(pymap(values), pyInt(Lit(0, int)), pymap(upper))
    case Ast.slice.Slice(None, None, None) =>
      pySlice(
        pymap(values),
        pyInt(Lit(0, int)),
        pyInt(pyGetLength(pymap(values)))
      )
    case _ =>
      cuvee.error("Currently only default steps for slice are supported.");
  }

  def call(func: Ast.identifier, args: Seq[Ast.expr]): Expr = func.name match {
    case "old"            => Old(pymap(args(0)))
    case "out" | "result" => pyResult
    case "len"            => pyInt(pyGetLength(pymap(args(0))))
    case "imp"            => pyImplies(pymap(args(0)), pymap(args(1)))
    case "forall" =>
      args match {
        case Seq(
              elem,
              Ast.expr
                .Lambda(
                  Ast.arguments(arguments: Seq[Ast.expr.Name], _, _, _),
                  body
                )
            ) =>
          pyBool(
            Forall(
              arguments.toList map formal,
              pyIsTrue(
                pyImplies(
                  pyBool(conditions(arguments.toList, elem)),
                  pymap(body)
                )
              )
            )
          )
      }
    case "exists" =>
      args match {
        case Seq(
              elem,
              Ast.expr
                .Lambda(
                  Ast.arguments(arguments: Seq[Ast.expr.Name], _, _, _),
                  body
                )
            ) =>
          pyBool(
            Exists(
              arguments.toList map formal,
              pyIsTrue(
                pyImplies(
                  pyBool(conditions(arguments.toList, elem)),
                  pymap(body)
                )
              )
            )
          )
      }
  }

  def formal(name: Ast.expr.Name) = Var(name.id.name, value)

  /* Builds boundaries for targets of quanitifers.
   * e.g. forall x. 0 <= x < array.Length
   */
  def conditions(names: List[Ast.expr.Name], elem: Ast.expr): Expr = {
    val isPyInt =
      names flatMap (x => List(Is(pymap(x), pyInt))) // TODO other types?
    val boundaries = names flatMap (x =>
      List(
        pyIsTrue(pyLessEquals(pyInt(Lit(0, int)), pymap(x))),
        pyIsTrue(
          pyLessThan(pymap(x), pyInt(pyGetLength(pymap(elem))))
        )
      )
    )
    And(isPyInt ++ boundaries)
  }

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
    case _                       => Var(id.name, value)
  }
}

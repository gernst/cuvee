package cuvee.python

import pythonparse.Ast
import cuvee.pure.Var
import cuvee.pure.Expr
import cuvee.pure.And
import cuvee.pure.Not
import cuvee.imp.Skip
import cuvee.imp.Prog
import cuvee.imp.Spec
import cuvee.imp.Block
import cuvee.imp.Break
import cuvee.imp.While
import cuvee.imp.If
import cuvee.imp.Call
import cuvee.imp.Assign

object spec {
  def input(args: Ast.arguments): List[Var] = {
    args.args.collect {
      case Ast.expr.Name(id, _) if id.name != "self" => Var(id.name, value)
    }.toList
  }

  def output(body: Seq[Ast.stmt]): List[Var] = {
    if (existsReturn(body)) List(pyResult) else Nil
  }

  def existsReturn(body: Seq[Ast.stmt]): Boolean = body match {
    case Nil                        => false
    case Ast.stmt.Return(_) :: next => true
    case Ast.stmt.While(_, bd, orelse) :: next =>
      existsReturn(bd.toList) || existsReturn(orelse.toList) || existsReturn(
        next
      )
    case Ast.stmt.If(_, bd, orelse) :: next =>
      existsReturn(bd.toList) || existsReturn(orelse.toList) || existsReturn(
        next
      )
    case _ :: next => existsReturn(next)
  }

  // Spec(xs: List[Var], pre: Expr, post: Expr) in imp/Prog.scala
  def body(body: Seq[Ast.stmt], in: List[Var]): (Option[Spec], Prog) = {
    val (vars, pre, post, remnant) = getSpec(body, in)
    val spec = Spec(vars, And(pre), And(post))
    val prog = Block(remnant)
    (Option(spec), prog)
  }

  def getSpec(
      body: Seq[Ast.stmt],
      in: List[Var]
  ): (List[Var], List[Expr], List[Expr], List[Prog]) =
    body match {
      case Nil => (Nil, Nil, Nil, Nil)
      case assign @ Ast.stmt
            .Assign(Seq(Ast.expr.Name(identifier, _)), _) :: next =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        val id = Var(identifier.name, value)
        if (!(in.map(_.name) contains id.name)) {
          (
            Var(id.name, value) :: vars,
            pre,
            post,
            stmts(assign.head) :: remnant
          )
        } else {
          (vars, pre, post, stmts(assign.head) :: remnant)
        }
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next if id.name == "requires" =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pyIsTrue(cExpr.pymap(arg)) :: pre, post, remnant)
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next if id.name == "ensures" =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pre, pyIsTrue(cExpr.pymap(arg)) :: post, remnant)
      case head :: next =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pre, post, stmts(head) :: remnant)
    }

  def stmts(stmt: Ast.stmt): Prog = stmt match {
    case Nil                      => Skip
    case Ast.stmt.Assert(test, _) => Spec.assert(pyIsTrue(cExpr.pymap(test)))
    case Ast.stmt.Assign(Seq(Ast.expr.Name(id, _)), values) =>
      Assign(List(Var(id.name, value)), List(cExpr.pymap(values)))
    case Ast.stmt.Assign(
          Seq(Ast.expr.Name(idOut, _)),
          Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _)
        ) if id.name != "len" =>
      Call(id.name, args.map(cExpr.pymap).toList, List(Var(idOut.name, value)))
    case Ast.stmt.Assign(
          Seq(
            Ast.expr.Attribute(
              Ast.expr.Name(Ast.identifier("self"), _),
              attr,
              _
            )
          ),
          values
        ) =>
      Assign(List(Var("self." + attr.name, value)), List(cExpr.pymap(values)))
    case Ast.stmt.Assign(
          Seq(
            Ast.expr.Subscript(
              Ast.expr.Attribute(
                Ast.expr.Name(Ast.identifier("self"), _),
                attr,
                _
              ),
              Ast.slice.Index(i),
              _
            )
          ),
          values
        ) =>
      Assign(
        List(Var("self." + attr.name, value)),
        List(
          cExpr.pyStore(
            Var("self." + attr.name, value),
            cExpr.pymap(i),
            cExpr.pymap(values)
          )
        )
      )
    case Ast.stmt.Assign(
          Seq(Ast.expr.Subscript(Ast.expr.Name(id, _), Ast.slice.Index(i), _)),
          values
        ) =>
      Assign(
        List(Var(id.name, value)),
        List(
          cExpr.pyStore(
            Var(id.name, value),
            cExpr.pymap(i),
            cExpr.pymap(values)
          )
        )
      )

    case Ast.stmt.Return(
          Some(Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _))
        ) =>
      Call(id.name, args.map(cExpr.pymap).toList, List(pyResult))
    case Ast.stmt.Return(Some(value)) =>
      Assign(List(pyResult), List(cExpr.pymap(value)))
    case Ast.stmt.Expr(Ast.expr.Call(name, Seq(args), _, _, _)) =>
      name match {
        case Ast.expr.Name(Ast.identifier("assume"), _) =>
          Spec.assume(pyIsTrue(cExpr.pymap(args)))
        case Ast.expr.Attribute(
              Ast.expr.Name(Ast.identifier("self"), _),
              attr,
              _
            ) =>
          Call(attr.name, Seq(args).map(cExpr.pymap).toList, Nil)
        case _ => cuvee.undefined
      }
    case Ast.stmt.If(test, body, orelse) =>
      If(
        pyIsTrue(cExpr.pymap(test)),
        Block(body.map(stmts).toList),
        Block(orelse.map(stmts).toList)
      )
    case Ast.stmt.While(test, body, orelse) =>
      val (inv, pre, post, decrease, remnant) = getInv(body)
      println("While")
      println(inv, pre, post, decrease, remnant)
      if (orelse.isEmpty) {
        println("decrease: " + And(decrease))
        While(
          // test: Expr,
          pyIsTrue(cExpr.pymap(test)),
          // body: Prog,
          Block(remnant),
          // term: Expr,
          And(decrease),
          // inv: Expr,
          if (inv.isEmpty) And(pre) else And(inv),
          // sum: Expr,
          pyIsTrue(pyNone()),
          // frames: List[Frame]
          Nil
        )
      } else {
        Block(
          List(
            While(
              pyIsTrue(cExpr.pymap(test)),
              Block(remnant),
              And(decrease),
              if (inv.isEmpty) And(pre) else And(inv),
              pyIsTrue(pyNone()),
              Nil
            ),
            If(
              Not(pyIsTrue(cExpr.pymap(test))),
              Block(orelse.map(stmts).toList),
              Skip
            )
          )
        )
      }
    case Ast.stmt.Break => Break
    case Ast.stmt.Pass  => Skip
    case _              => cuvee.undefined
  }

  def getInv(
      body: Seq[Ast.stmt]
  ): (List[Expr], List[Expr], List[Expr], List[Expr], List[Prog]) =
    body match {
      case Nil => (Nil, Nil, Nil, Nil, Nil)
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next =>
        id.name match {
          case "invariant" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (pyIsTrue(cExpr.pymap(arg)) :: inv, pre, post, decrease, remnant)
          case "requires" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pyIsTrue(cExpr.pymap(arg)) :: pre, post, decrease, remnant)
          case "ensures" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pre, pyIsTrue(cExpr.pymap(arg)) :: post, decrease, remnant)
          case "termination" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pre, post, pyGetInt(cExpr.pymap(arg)) :: decrease, remnant)
        }
      case head :: next =>
        val (inv, pre, post, decrease, remnant) = getInv(next)
        (inv, pre, post, decrease, stmts(head) :: remnant)
    }
}

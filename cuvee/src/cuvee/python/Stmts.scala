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
import cuvee.smtlib.DefineProc
import cuvee.pure.Param
import cuvee.smtlib.Cmd
import cuvee.imp.Return

class Stmts(val exprs: Exprs) {
  import exprs.sig._
  import exprs.pymap

  def createCmd(stmt: Ast.stmt): List[Cmd] = stmt match {
    case Ast.stmt.ImportFrom(module, _, _)
        if module == Option(Ast.identifier("help_methods")) =>
      Nil

    case Ast.stmt.FunctionDef(name, args, stmts, _) =>
      val in = input(args)
      val out = List(pyResult) // Stmt.output(body)
      val (spec, prog) = body(stmts, in)
      val param = Nil
      state.proc(name.name, param, in, out, spec)
      state.procdef(name.name, in, out, prog)

      val cmd = DefineProc(
        name.name,
        param,
        in,
        out,
        spec,
        prog
      )

      List(cmd)

    case Ast.stmt.ClassDef(name, bases, body, _) =>
      cuvee.error("Classes for python are currently not supported.")

    case _ =>
      cuvee.error("Unsupported statement: " + stmt)
  }

  def input(args: Ast.arguments): List[Var] = {
    args.args.collect {
      case Ast.expr.Name(id, _) if id.name != "self" => Var(id.name, value)
    }.toList
  }

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
      case assign @ Ast.stmt
            .Assign(Seq(Ast.expr.Name(identifier, _)), _) :: next =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        val id = Var(identifier.name, value)
        if (!(in.map(_.name) contains id.name)) {
          (
            Var(id.name, value) :: vars,
            pre,
            post,
            stmts(assign.head) ++ remnant
          )
        } else {
          (vars, pre, post, stmts(assign.head) ++ remnant)
        }
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next if id.name == "requires" =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pyIsTrue(pymap(arg)) :: pre, post, remnant)
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next if id.name == "ensures" =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pre, pyIsTrue(pymap(arg)) :: post, remnant)
      case head :: next =>
        val (vars, pre, post, remnant) = getSpec(next, in)
        (vars, pre, post, stmts(head) ++ remnant)
      case Nil => (Nil, Nil, Nil, Nil)
    }

  def stmts(stmt: Ast.stmt): List[Prog] = stmt match {
    case Ast.stmt.Assert(test, _) => List(Spec.assert(pyIsTrue(pymap(test))))
    case Ast.stmt.Assign(Seq(Ast.expr.Name(id, _)), values) =>
      List(Assign(List(Var(id.name, value)), List(pymap(values))))
    case Ast.stmt.Assign(
          Seq(Ast.expr.Name(idOut, _)),
          Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _)
        ) if id.name != "len" =>
      List(Call(id.name, args.map(pymap).toList, List(Var(idOut.name, value))))
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
      List(Assign(List(Var("self." + attr.name, value)), List(pymap(values))))
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
      List(
        Assign(
          List(Var("self." + attr.name, value)),
          List(
            pyStore(
              Var("self." + attr.name, value),
              pymap(i),
              pymap(values)
            )
          )
        )
      )
    case Ast.stmt.Assign(
          Seq(Ast.expr.Subscript(Ast.expr.Name(id, _), Ast.slice.Index(i), _)),
          values
        ) =>
      List(
        Assign(
          List(Var(id.name, value)),
          List(
            pyStore(
              Var(id.name, value),
              pymap(i),
              pymap(values)
            )
          )
        )
      )
    case Ast.stmt.Return(
          Some(Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _))
        ) =>
      List(Call(id.name, args.map(pymap).toList, List(pyResult)), Return)
    case Ast.stmt.Return(None) =>
      List(Return)
    case Ast.stmt.Return(Some(value)) =>
      List(Assign(List(pyResult), List(pymap(value))), Return)
    case Ast.stmt.Expr(Ast.expr.Call(name, Seq(args), _, _, _)) =>
      name match {
        case Ast.expr.Name(Ast.identifier("assume"), _) =>
          List(Spec.assume(pyIsTrue(pymap(args))))
        case Ast.expr.Attribute(
              Ast.expr.Name(Ast.identifier("self"), _),
              attr,
              _
            ) =>
          List(Call(attr.name, Seq(args).map(pymap).toList, Nil))
        case _ => cuvee.undefined
      }
    case Ast.stmt.If(test, body, orelse) =>
      List(
        If(
          pyIsTrue(pymap(test)),
          Block(body.flatMap(stmts).toList),
          Block(orelse.flatMap(stmts).toList)
        )
      )
    case Ast.stmt.While(test, body, orelse) =>
      val (inv, pre, post, decrease, remnant) = getInv(body)

      val loop = While(
        pyIsTrue(pymap(test)),
        Block(remnant),
        And(decrease),
        if (inv.isEmpty) And(pre) else And(inv),
        pyIsTrue(pyNone()),
        Nil
      )

      if (orelse.isEmpty) List(loop)
      else {
        val after = If(
          Not(pyIsTrue(pymap(test))),
          Block(orelse.flatMap(stmts).toList),
          Skip
        )
        List(Block(List(loop, after)))
      }
    case Ast.stmt.Break => List(Break)
    case Ast.stmt.Pass  => List(Skip)
    case Nil            => List(Skip)
    case _              => cuvee.error("Unsupported statement: " + stmt)
  }

  def getInv(
      body: Seq[Ast.stmt]
  ): (List[Expr], List[Expr], List[Expr], List[Expr], List[Prog]) =
    body match {
      case Ast.stmt.Expr(
            Ast.expr.Call(Ast.expr.Name(id, _), Seq(arg), _, _, _)
          ) :: next =>
        id.name match {
          case "invariant" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (pyIsTrue(pymap(arg)) :: inv, pre, post, decrease, remnant)
          case "requires" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pyIsTrue(pymap(arg)) :: pre, post, decrease, remnant)
          case "ensures" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pre, pyIsTrue(pymap(arg)) :: post, decrease, remnant)
          case "termination" =>
            val (inv, pre, post, decrease, remnant) = getInv(next)
            (inv, pre, post, pyGetInt(pymap(arg)) :: decrease, remnant)
        }
      case head :: next =>
        val (inv, pre, post, decrease, remnant) = getInv(next)
        (inv, pre, post, decrease, stmts(head) ++ remnant)
      case Nil => (Nil, Nil, Nil, Nil, Nil)
    }
}

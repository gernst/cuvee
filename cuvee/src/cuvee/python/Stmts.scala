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
  import exprs.sugar

  def createCmd(stmt: Ast.stmt): List[Cmd] = stmt match {
    case Ast.stmt.ImportFrom(module, _, _) if module == Option(Ast.identifier("cuvee")) =>
      Nil

    case Ast.stmt.FunctionDef(name, args, stmts, _) =>
      val in = input(args)
      val out = List(pyResult) // Stmt.output(body)
      val (spec, prog) = body(stmts, in)
      val param = Nil
      state.proc(name.name, param, in, out, spec)
      state.procdef(name.name, in, out, prog)

      val cmd = DefineProc(name.name, param, in, out, spec, prog)

      List(cmd)

    case Ast.stmt.ClassDef(name, bases, body, _) =>
      cuvee.error("Classes for python are currently not supported.")

    case _ =>
      cuvee.error("Unsupported statement: " + stmt)
  }

  def input(args: Ast.arguments): List[Var] = {
    args.args.toList.collect {
      case Ast.expr.Name(id, _) if id.name != "self" =>
        Var(id.name, pyValue)
    }
  }

  def body(body: Seq[Ast.stmt], in: List[Var]): (Option[Spec], Prog) = {
    val (pre, post, remnant) = getSpec(body)
    val spec = Spec(List(pyResult), And(pre), And(post))
    val prog = Block(remnant)

    (Option(spec), prog)
  }

  def getSpec(body: Seq[Ast.stmt]): (List[Expr], List[Expr], List[Prog]) = body match {
    case Ast.stmt.Expr(sugar.Call("requires", args)) :: rest =>
      val (pre, post, remnant) = getSpec(rest)
      val phis = args.toList map { arg => pyIsTrue(pymap(arg)) }
      (phis ++ pre, post, remnant)

    case Ast.stmt.Expr(sugar.Call("ensures", args)) :: rest =>
      val (pre, post, remnant) = getSpec(rest)
      val phis = args.toList map { arg => pyIsTrue(pymap(arg)) }
      (pre, phis ++ post, remnant)

    case _ =>
      (Nil, Nil, body.toList flatMap stmts)
  }

  def stmts(stmt: Ast.stmt): List[Prog] = stmt match {
    case Ast.stmt.Assert(test, _) =>
      List(Spec.assert(pyIsTrue(pymap(test))))

    case Ast.stmt.Assign(Seq(Ast.expr.Name(id, _)), rhs) =>
      List(Assign(List(Var(id.name, pyValue)), List(pymap(rhs))))

    case Ast.stmt.Assign(
          Seq(Ast.expr.Name(lhs, _)),
          Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _)
        ) if id.name != "len" =>
      List(Call(id.name, args.map(pymap).toList, List(Var(lhs.name, pyValue))))

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
      List(Assign(List(Var("self." + attr.name, pyValue)), List(pymap(values))))

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
          List(Var("self." + attr.name, pyValue)),
          List(
            pyStore(
              Var("self." + attr.name, pyValue),
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
          List(Var(id.name, pyValue)),
          List(
            pyStore(
              Var(id.name, pyValue),
              pymap(i),
              pymap(values)
            )
          )
        )
      )

    case Ast.stmt.Break => List(Break)
    case Ast.stmt.Pass  => Nil

    case Ast.stmt.Return(Some(Ast.expr.Call(Ast.expr.Name(id, _), args, _, _, _))) =>
      List(Call(id.name, args.toList map pymap, List(pyResult)), Return)

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
        case _ =>
          cuvee.undefined
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
      val (inv, sum, List(term), remnant) = getInv(body)

      val loop = While(
        pyIsTrue(pymap(test)),
        Block(remnant),
        term,
        And(inv),
        And(sum),
        Nil
      )

      if (orelse.isEmpty) {
        List(loop)
      } else {
        val after = If(
          Not(pyIsTrue(pymap(test))),
          Block(orelse.toList flatMap stmts),
          Skip
        )
        List(Block(List(loop, after)))
      }
    // case Nil            => Nil
    case _ => cuvee.error("Unsupported statement: " + stmt)
  }

  def getInv(body: Seq[Ast.stmt]): (List[Expr], List[Expr], List[Expr], List[Prog]) =
    body match {
      case Ast.stmt.Expr(sugar.Call("invariant", args)) :: rest =>
        val (inv, post, term, remnant) = getInv(rest)
        val phis = args.toList map { arg => pyIsTrue(pymap(arg)) }
        (phis ++ inv, post, term, remnant)

      case Ast.stmt.Expr(sugar.Call("summary", args)) :: rest =>
        val (pre, post, term, remnant) = getInv(rest)
        val phis = args.toList map { arg => pyIsTrue(pymap(arg)) }
        (pre, phis ++ post, term, remnant)

      case Ast.stmt.Expr(sugar.Call("decreases", Seq(arg))) :: rest =>
        val (inv, post, term, remnant) = getInv(rest)
        (inv, post, pyGetInt(pymap(arg)) :: term, remnant)

      case _ =>
        (Nil, Nil, Nil, body.toList flatMap stmts)
    }
}

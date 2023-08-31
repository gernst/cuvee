package cuvee

import cuvee.util._
import cuvee.pure._
import cuvee.smtlib._
import java.io.PrintStream
import java.io.FileOutputStream
import java.io.OutputStream

package object lemmas {
  def read(file: String) = {
    if (file endsWith ".smt2")
      smtlib.parse(file)
    else if (file endsWith ".bpl")
      boogie.parse(file)
    else
      cuvee.error("unknown file format: " + file)
  }

  def prepare(cmds: List[Cmd], st: State) = {
    for (
      DeclareDatatypes(arities, dts) <- cmds;
      ((name, arity), dt) <- arities zip dts
    ) {
      st.datatype(name, dt)
    }

    val decl =
      for (DeclareFun(name, params, args, res) <- cmds)
        yield st.funs(name, args.length)
    val defn =
      for (DefineFun(name, params, args, res, _, _) <- cmds)
        yield st.funs(name, args.length)

    val eqs0 =
      for (
        Assert(expr) <- cmds;
        eq <- Rules.from(expr, decl.toSet)
      )
        yield eq

    val eqs1 =
      for (
        DefineFun(name, params, formals, res, body, _) <- cmds;
        fun = st.funs(name, formals.length);
        eq <- Rules.from(fun, formals, body, defn.toSet)
      )
        yield eq

    val eqs = eqs0 ++ eqs1

    val decls1 =
      for (decl @ DeclareFun(_, _, _, _) <- cmds)
        yield decl

    val decls2 =
      for (DefineFun(name, params, args, res, _, _) <- cmds)
        yield DeclareFun(name, params, args.types, res)

    val dfs =
      for ((fun, stuff) <- eqs.groupBy(_.fun))
        yield {
          val cases =
            for (Rule(App(_, args), body, guard, Nil) <- stuff)
              yield C(args, And.flattenStrong(guard), body)
          Def(fun, cases)
        }

    (decls1 ++ decls2, dfs.toList)
  }

  def dump(out: PrintStream, syntax: util.Syntax, comment: Boolean = false) {
    for (line <- syntax.lines) {
      if (comment)
        out.print("; ")
      out.println(line)
    }
    out.println()
  }

  def dump(out: PrintStream, section: String, stuff: List[Any]) {
    if (stuff.nonEmpty) {
      out.println(section)
      for (item <- stuff)
        out.println("  " + item)
      out.println()
    }
  }

  def log(file: String) = {
    new PrintStream(new FileOutputStream(file))
  }

  object nullOutputStream extends OutputStream {
    def write(b: Int) {}
  }

  val NO = new PrintStream(nullOutputStream)

  /** The default printer to use: Prints s-expressions */
  implicit val printer: cuvee.util.Printer = cuvee.sexpr.Printer

  def vars(exprs: List[Expr]): List[Var] = {
    exprs flatMap vars
  }

  def vars(expr: Expr): List[Var] = expr match {
    case x: Var          => List(x)
    case l: Lit          => Nil
    case App(inst, args) => vars(args)
  }
}

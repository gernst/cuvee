package cuvee.util

import scala.collection.mutable

import cuvee.pipe.Sink
import cuvee.State
import cuvee.smtlib._
import cuvee.pure._
import cuvee.imp._
import java.io.PrintStream
import java.io.FileOutputStream
import java.io.File

object JavaBenchmarkWriter {
  val Indent = "    "
  val Package = "analysis.benchmarks"

  def indent(lines: List[String]) = {
    for (line <- lines)
      yield Indent + line
  }

  def quote(str: String): String = {
    "\"" + str + "\""
  }

  def quote(strs: Iterable[String]): Iterable[String] = {
    strs map quote
  }

  sealed trait Gen
  case class Str(str: String) extends Gen
  case class Num(int: BigInt) extends Gen
  case class Make(fun: String, args: List[Gen]) extends Gen

  def atom(int: BigInt) = {
    Num(int)
  }

  def atom(str: String) = {
    Str(str)
  }

  def call(fun: String, args: List[Gen]) = {
    Make(fun, args)
  }

  def call(fun: String, args: Gen*) = {
    Make(fun, args.toList)
  }

  def block(progs: List[Gen]): Gen = {
    call("program.block", call("List.of", progs))
  }

  def sink(path: String) = (_: Printer) =>
    new Sink {
      var integers: Set[String] = Set()
      var arrays: Set[String] = Set()
      var proc: Proc = _
      var prog: Prog = _

      def exec(cmd: Cmd, state: State) = cmd match {
        // ignore C prelude
        case DeclareDatatypes(List((Name("c#void", None), 0)), datatypes) =>
          Success
        case DeclareSort(Name("c#ptr", None), arity) =>
          Success
        case DeclareSort(Name("c#heap", None), arity) =>
          Success
        case DeclareVar(Name("c#heap", None), typ) =>
          Success
        case DeclareFun(Name("c#bitand", None), params, args, res) =>
          Success
        case DeclareFun(Name("c#bitor", None), params, args, res) =>
          Success
        case DeclareProc(Name("malloc", None), params, in, out, spec) => 
          Success

        case DeclareVar(Name(name, None), Sort.int) =>
          integers += name
          Success

        case DeclareVar(Name(name, None), Sort(Con.array, List(Sort.int, Sort.int))) =>
          arrays += name
          Success

        case DefineProc(name @ Name("main", None), params, in, out, spec, body) =>
          proc = Proc(name, params, in, out, spec)
          prog = body
          Success

        case DefineProc(name, params, in, out, spec, body) =>
          // ignore --- should be inlined anyway
          Success
      }

      // def process(state: State, expr: Expr): String = expr match {
      //   case Lit(any, typ)                   => ???
      //   case Post(how, prog, post)           => ???
      //   case Is(arg, fun)                    => ???
      //   case Var(name, typ)                  => ???
      //   case Bind(quant, formals, body, typ) => ???
      //   case Distinct(exprs)                 => ???
      //   case At(where, arg)                  => ???
      //   case Match(expr, cases, typ)         => ???
      //   case Let(eqs, body)                  => ???
      //   case Note(expr, attr)                => ???
      //   case App(inst, args)                 => ???
      // }

      def process(expr: Expr): Gen = expr match {
        case x: Var =>
          call("program.variable", atom(x.toString))

        case Lit(i: BigInt, _) =>
          call("program.contant", atom(i))

        case Plus(args) =>
          val args_ = args map process
          call("program.addition", call("Set.of", args_))

        case Times(args) =>
          val args_ = args map process
          call("program.multiplication", call("Set.of", args_))

        case Minus(left, right) =>
          call("program.subtraction", process(left), process(right))

        case DivBy(left, right) =>
          call("program.division", process(left), process(right))

        case Mod(left, right) =>
          call("program.modulo", process(left), process(right))

        case Le(left, right) =>
          call("program.lessEqualThan", process(left), process(right))

        case Lt(left, right) =>
          call("program.lessThan", process(left), process(right))

        case Gt(left, right) =>
          call("program.greaterThan", process(left), process(right))

        case Ge(left, right) =>
          call("program.greaterEqualThan", process(left), process(right))

        case Not(Eq(left, right)) =>
          call("program.unequalTo", process(left), process(right))

        case Eq(left, right) =>
          call("program.equalTo", process(left), process(right))

        case Select(base, index) =>
          call("program.arrayElement", process(base), process(index))
      }

      def process(state: State, prog: Prog): List[Gen] = prog match {
        case Return =>
          List(call("program.stop"))

        case Assign(List(a), List(Store(b, i, e))) if a == b =>
          val ai_ = call("program.arrayElement", process(a), process(i))
          List(call("program.assign", ai_, process(e)))

        case Assign(List(x), List(e)) =>
          List(call("program.assign", process(x), process(e)))

        case Local(xs, Nil) =>
          xs foreach {
            case x@Var(name, Sort.int) =>
              integers += x.toString
            case x@Var(name, Sort(Con.array, List(Sort.int, Sort.int))) =>
              arrays += x.toString
            case x => 
              cuvee.error("unsupported variable: " + x.toStringTyped)
          }

          Nil

        case Local(xs, es) =>
          process(state, Block(List(Local(xs, Nil), Assign(xs, es))))

        case Call(name, in, out) =>
          val (xs, zs, body) = state procdefs name
          val re = Expr.subst(zs, out)
          val body_ = body replace re
          val block = Block(List(Local(xs, Nil), Assign(xs, in), Spec.havoc(out), body_))
          process(state, block)

        // assert
        case Spec(Nil, pre, True) =>
          List(call("program.assert", process(pre)))

        // assume
        case Spec(Nil, True, post) =>
          List(call("program.assume", process(post)))

        // havoc
        case Spec(List(x), True, True) =>
          List(call("program.havoc", process(x)))

        case If(test, left, right) =>
          val test_ = process(test)
          val left_ = process(state, left)
          val right_ = process(state, right)
          List(call("program.if_", test_, block(left_), block(right_)))

        case While(test, body, term, inv, sum, frames) =>
          val test_ = process(test)
          val body_ = process(state, body)
          List(call("program.while_", test_, block(body_)))

        case Block(progs) =>
          for (
            prog <- progs;
            res <- process(state, prog)
          )
            yield res
      }

      // don't add newline at the end
      def format(file: PrintStream, indent: String, res: Gen): Unit = res match {
        case Num(int) =>
          file.print(indent + int)

        case Str(str) =>
          file.print(indent + quote(str))

        case Make(fun, List(Num(int))) =>
            file.print(indent + fun + "(" + int + ")")

        case Make(fun, List(Str(str))) =>
            file.print(indent + fun + "(" + quote(str) + ")")

        case Make(fun, args) =>
          if (args.isEmpty) {
            file.print(indent + fun + "()")
          } else {
            file.println(indent + fun + "(")
            for ((arg, first, last) <- args.zipWithFirstLast) {
              format(file, indent + Indent, arg)

              if (!last)
                file.println(",")
              else
                file.print(")")
            }
          }
      }

      def done(state: State) {
        try {
        val file = new PrintStream(new FileOutputStream(path))
        var klass = path
        klass = klass dropRight 5
        klass = klass drop ((klass lastIndexOf "/") + 1)


        file.println("package " + Package + ";")
        file.println()

        file.println("import java.util.List;")
        file.println("import java.util.Set;")
        file.println()

        file.println("import analysis.common.builder.Benchmark;")
        file.println("import analysis.common.builder.BenchmarkProgram;")
        file.println()

        file.println("class " + klass + " implements Benchmark {")

        file.println(
          Indent + "<ExpressionT, ConditionT, StatementT, AssignableT extends ExpressionT> StatementT statement(BenchmarkProgram<ExpressionT, ConditionT, StatementT, AssignableT> program) {"
        )

        file.println(Indent * 2 + "return")
        format(file, Indent * 3, block(process(state, prog)))
        file.println(";")

        file.println(Indent + "}")
        file.println()

        file.println(Indent + "List<String> integerVariables() {")
        file.println(quote(integers).mkString(Indent * 2 + "return List.of(", ", ", ");"))
        file.println(Indent + "}")
        file.println()

        file.println(Indent + "List<String> arrayVariables() {")
        file.println(quote(arrays).mkString(Indent * 2 + "return List.of(", ", ", ");"))
        file.println(Indent + "}")
        file.println()

        file.println("}")
        } catch {
          case e: Throwable =>
            val rm = new File(path)
            rm.delete()
        }
      }
    }
}

package cuvee.boogie

import cuvee.error
import cuvee.util
import cuvee.pure._
import cuvee.util.Name
import cuvee.smtlib.Res
import cuvee.smtlib
import cuvee.imp.Prog
import cuvee.imp._
import cuvee.smtlib._

trait Syntax extends util.Syntax {
  def bexpr: List[Any]
}

object Printer extends cuvee.util.Printer {

  def lines(cmd: Cmd): List[String] = cmd match {
    case Labels => cuvee.undefined
    case SetLogic(logic) =>
      List("/* ", "Command unsupported in boogie:", "set-logic", logic, " */")
    case SetOption(attr, arg) =>
      List(
        "/* ",
        "Command unsupported in boogie:",
        "set-option",
        attr,
        arg.toString,
        " */"
      )
    case GetInfo(attr) =>
      List("/* ", "Command unsupported in boogie:", "get-info", attr, " */")
    case SetInfo(attr, _) =>
      List("/* ", "Command unsupported in boogie:", "set-info", attr, " */")
    case Push(depth) => cuvee.undefined
    case Pop(depth)  => cuvee.undefined
    case GetModel    => cuvee.undefined
    case Exit        => cuvee.undefined
    case Reset       => cuvee.undefined
    case Assert(expr) =>
      expr match {
        case Bind(quant, formals, body, _) =>
          List(
            "axiom " + quant.name + formals
              .map(_.toStringTyped)
              .mkString(" ", ", ", " :: "),
            body + ";"
          )
        case _ =>
          List("axiom " + expr + ";")
      }
    case Lemma(expr, tactic, _) =>
      tactic match {
        case None         => List("lemma " + expr + ";")
        case Some(tactic) => List("lemma " + expr, "proof" + tactic + ";")
      }
    case CheckSat                  => cuvee.undefined
    case DeclareSort(name, arity)  => List("type " + name + ";") // add params
    case DefineSort(name, _, body) => List("type " + name + " = " + body + ";")
    case x @ DeclareFun(name, params, _, res) =>
      List(
        "function " + name + "(" + x.formals.toStringTyped + "): " + res + ";"
      )
    case DefineFun(name, _, formals, res, body, _) =>
      List(
        "function " + name + "(" + formals.toStringTyped + "): " + res + "{",
        "  " + body,
        "}"
      )
    case DeclareDatatypes(arities, datatypes) =>
      val lines = arities zip datatypes map {
        case ((name, arity), Datatype(Nil, constrs)) =>
          val cs = constrs map {
            case (constr, Nil) =>
              constr.name
            case (constr, sels) =>
              val as = sels map { case Fun(name, _, _, res) =>
                name + ": " + res
              }
              constr.name + as.mkString("(", ", ", ")")
          }
          name + cs.mkString(" = ", " | ", ";")

        case ((name, arity), Datatype(params, constrs)) =>
          val cs = constrs map {
            case (constr, Nil) =>
              constr.name
            case (constr, sels) =>
              val as = sels map { case Fun(name, _, _, res) =>
                name + ": " + res
              }
              constr.name + as.mkString("(", ", ", ")")
          }
          name + params.mkString("<", ", ", ">") + cs.mkString(
            " = ",
            " | ",
            ";"
          )
      }
      "data " :: lines
    case DeclareProc(name, params, in, out, spec)      => cuvee.undefined
    case DefineProc(name, params, in, out, spec, body) => cuvee.undefined
  }

  def lines(syn: util.Syntax): List[String] = ???

  // TODO use lines in the appropriate places instead of var.toString
  def lines(prog: Prog): List[String] = prog match {
    case Block(progs) => ???
    case Break        => List("break;")
    case Return       => List("return;")
    case Local(xs, rhs) =>
      List("var " + xs + ": " + xs.types + " := " + rhs + ";")
    case Assign(xs, rhs)       => List(xs + " := " + rhs)
    case Spec(xs, pre, post)   => ???
    // TODO right may be empty
    case If(test, left, right) => List("if(" + test + ") {", left.toString, "} else " + right, "}")
    // TODO term, inv, sum, frames nay be empty
    case While(test, body, term, inv, sum, frames) =>
      List(
        "while(" + test + ")",
        "decreases " + term,
        "invariant " + inv,
        "summary " + sum,
        "frames " + frames,
        body.toString // TODO
      )
    case Call(name, in, out) => ???
  }

  def lines(any: Any): List[String] = any match {
    // Boolean values
    case true  => List("true")
    case false => List("false")
    // Numbers
    case i: Int    => List(i.toString)
    case i: BigInt => List(i.toString)
    case f: Float  => List(f.toString)
    // Name
    case n: Name           => List(n.toLabel)
    case smtlib.Error(msg) => List(msg.mkString("\"", " ", "\""))
    case res: Res          => List(res.toString())
    // Props
    case p: Prop => (p.bexpr map (_.toString))
    // Syntax (recursive call on the syntax' s-expression)
    case s: Syntax => lines(s.bexpr)
    // String (= Id)
    case s: String => List(s)
    // Pairs and lists consist of tokens and more syntax elements
    // Call lines on the elements recursively
    case (a, b) => lines(a) ++ lines(b)
    case xs: List[_] =>
      val args = xs flatMap lines
      val max = args.maxBy(_.length)
      val sum = args.foldLeft(0)(_ + _.length)

      val break =
        args.length >= 2 && (max.length > 20 || sum >= 80)

      if (break && false) {
        args
      } else {
        List(args.mkString(""))
      }
    // Fall-through: just crash
    // case _ => List()
  }
}

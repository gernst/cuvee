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
import cuvee.boogie

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
            "  " + body + ";"
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
        "function " + name +
          "(" + x.formals.toStringTyped.toLowerCase + "): " +
          res.toString.toLowerCase + ";"
      )
    case DefineFun(name, _, formals, res, body, _) =>
      List(
        "function " + name +
          "(" + formals.toStringTyped.toLowerCase + "): " +
          res + "{",
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
    case DefineProc(name, params, in, out, spec, body) =>
      // TODO what is 'params' and how does 'out' look?
      val rest = "{" +: lines(body) :+ "}"
      in match {
        case Nil =>
          ("procedure " + name + "()") +: rest
        case _ =>
          val header =
            List(
              "procedure " + name + "(" + in.toStringTyped.toLowerCase + ")"
            )
          spec match {
            case None =>
              header ++ rest
            case Some(s) =>
              val spec_ = lines(s)
              header ++ spec_ ++ rest
          }
      }
  }

  def lines(prog: Prog): List[String] = prog match {
    case Block(progs) => indent(progs flatMap lines)
    case Break        => List("break;")
    case Return       => List("return;")
    case Local(xs, rhs) =>
      val vars = for (x <- xs) yield x + ": " + x.typ
      val exprs = for (e <- rhs) yield lines(e)
      List(
        "var " + vars.mkString(", ") +
          " := " + exprs.flatten.mkString(", ") + ";"
      )
    case Assign(xs, rhs) =>
      val exprs = for (e <- rhs) yield lines(e)
      List(xs.mkString(",") + " := " + exprs.flatten.mkString(",") + ";")
    case Spec(xs, pre, post) =>
      (xs, pre, post) match {
        case (Nil, True, phi) => indent(List("assert " + phi + ";"))
        case (Nil, phi, True) => indent(List("assume " + phi + ";"))
        case (xs, True, True) => indent(List("havoc " + xs.mkString(", ")))
        case _ =>
          List(
            "/* ",
            "Unknown Spec in boogie:",
            xs.mkString(", "),
            pre.toString,
            post.toString,
            " */"
          )
      }
    case x @ If(test, left, right) => if_(x)
    case While(test, body, term, inv, sum, frames) =>
      val con = "while(" + lines(test) + ")"

      var spec: List[String] = List()
      if (term != Zero)
        spec = spec :+ ("decreases\t" + lines(term).mkString + ";")
      if (inv != True)
        spec = spec :+ ("invariant\t" + lines(inv).mkString + ";")
      if (sum != True)
        spec = spec :+ ("summary\t" + lines(sum).mkString + ";")
      if (!frames.isEmpty)
        spec = spec :+ ("frames\t" + lines(frames).mkString + ";")

      val body_ = "{" +: lines(body) :+ "}"

      (con +: indent(spec)) ++ body_
    case Call(name, in, out) => ???
  }

  def lines(expr: Expr): List[String] = expr match {
    case Lit(any, typ)   => List(any.toString)
    case Var(name, typ)  => List(name.toString)
    case App(inst, Nil)  => List(inst.toString)
    case App(inst, args) =>
      // TODO I am not sure about this
      if (inst.toString == "old") {
        List(expr.toString)
      } else {
        val (assoc, prec) = precedence(expr)
        List(format(expr, prec, assoc))
      }
    case Bind(quant, formals, body, typ) => ???
    case Distinct(exprs)                 => ???
    case Is(arg, fun)                    => ???
    case Let(eqs, body)                  => ???
    case Match(expr, cases, typ)         => ???
    case Note(expr, attr)                => ???
  }

  def lines(any: Any): List[String] = any match {
    case cmd: Cmd   => lines(cmd)
    case prog: Prog => lines(prog)
    case expr: Expr => lines(expr)
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

  /** When printing an infix application such as `a + b` the information from
    * prec and assoc is used to decide whether parentheses are needed.
    *
    * For example `(a + b) * c` needs parentheses because context `_ * c` has a
    * strictly higher precedence than `+` .assoc is only necessary when prec is
    * the same as the current function.
    *
    * @param expr
    *   to print
    * @param prec
    *   is the precedence of the surrounding context
    * @param assoc
    *   the associativity of the given expr
    * @return
    *   String to print for the given expr
    */
  private def format(expr: Expr, prec: Int, assoc: easyparse.Assoc): String =
    // TODO add prec/ assoc
    // idea: lookahead in arguments
    expr match {
      // Logical connectives
      case And(phis) =>
        val args = phis map lines
        (args.flatten).mkString(" && ")
      case Or(phis) =>
        val args = phis map lines
        (args.flatten).mkString(" || ")
      // Infix operators
      case App(inst, List(left, right))
          if Expr.boogieInfix contains inst.toString =>
        // look in left/ right to see ops
        ((lines(left) :+ inst.toString) ++ lines(right)).mkString(" ")
      case _ => expr.toString
    }

  /** Provides a tuple containing associativity as well as precedence for the
    * given expression.
    *
    * @param expr
    *   to get prec an assoc for
    * @return
    *   associativity and precedence for the given expr
    */
  private def precedence(expr: Expr): (easyparse.Assoc, Int) = {
    val map = boogie.Grammar.syntax.infix_ops
    val App(inst, args) = expr

    var operator = ""
    if (map.contains(inst.toString)) {
      operator = inst.toString
    } else {
      operator =
        boogie.Parser.translate.filter(_._2 == inst.toString).map(_._1).head
    }
    map.get(operator).get
  }

  private def if_(prog: If): List[String] = {
    val If(test, left, right) = prog
    val first = ("if(" + lines(test) + ") {") +: lines(left)
    right match {
      case x @ If(test_, left_, right_) =>
        (first :+ "} else " + if_(x).head) ++ if_(x).tail
      case Block(Nil)   => first :+ "}"
      case x @ Block(_) => (first :+ "} else {") ++ (lines(x) :+ "}")
      case _ => first :+ ("// Unknown operation in If: " ++ right.toString)
    }
  }

  private def indent(lines: List[String]): List[String] =
    for (l <- lines) yield "  " + l
}

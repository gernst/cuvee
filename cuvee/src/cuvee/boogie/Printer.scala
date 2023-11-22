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
  import easyparse.Assoc
  import easyparse.Non

  import boogie.Grammar.syntax
  import boogie.Parser.translate

  // cuvee.name -> (boogie.name, assoc, prec)
  private val infix =
    for ((k, v) <- syntax.infix_ops) yield {
      val (assoc, prec) = v
      var key = "";
      translate.get(k) match {
        case Some(s) => key = s
        case None    => key = k
      }
      key -> (k, prec, assoc)
    }
  private val prefix =
    for ((k, v) <- syntax.prefix_ops) yield {
      var key = "";
      translate.get(k) match {
        case Some(s) => key = s
        case None    => key = k
      }
      key -> (k, v, Non)
    }

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
      val exprs = for (e <- rhs) yield lines(e).mkString
      List(xs.mkString(",") + " := " + exprs.mkString(",") + ";")
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
      val con = "while(" + lines(test).mkString + ")"

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

  // TODO: return single String
  def lines(expr: Expr): List[String] = expr match {
    case Lit(any, typ)  => List(any.toString)
    case Var(name, typ) => List(name.toString)
    case App(inst, Nil) => List(inst.toString)
    // Map access
    case Select(arr, idx) =>
      List(lines(arr).mkString + "[" + lines(idx).mkString + "]")
    case Store(arr, idx, newval) =>
      val assign = (lines(idx) :+ ":=") ++ lines(newval)
      List(lines(arr).mkString + "[" + assign.mkString(" ") + "]")

    // TODO: only if necessary
    // case Old(arg) =>
    //   "old(" + arg + ")"

    // TODO: explicitly match unary and binary functions
    // case App(inst, List(left, right)) if infix contains inst.name =>
    //   val (name, prec, assoc) = infix(inst.name)
    //    var a = lines(left), b = lines(right)
    //    decide if we need parens around a and b
    //    val (aprec, aaosc) = precedence(left)
    //    if (aprec > prec || aprec == prec && aassoc != assoc) a = "(" + a + ")"
    // return a + " " + name + " " + b

    // Applications (i.e. function calls)
    // TODO how are these supposed to look? calls arent implemented in prog yet (same reason)
    case App(inst, args) =>
      val (assoc, prec) = precedence(expr)
      List(format(expr, prec, assoc))
    case Bind(quant, formals, body, typ) =>
      val vars = for (x <- formals) yield x + ": " + x.typ
      val quantifier = quant.toString + " " + vars.mkString(" ") + " :: "
      quantifier +: lines(body) :+ ";"
    case Distinct(exprs)         => ???
    case Is(arg, fun)            => ???
    case Let(eqs, body)          => ???
    case Match(expr, cases, typ) => ???
    case Note(expr, attr)        => ???
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
    expr match {
      // Logical connectives
      // TODO add prec/ assoc
      case And(phis) =>
        val args = phis map lines
        (args.flatten).mkString(" && ")
      case Or(phis) =>
        val args = phis map lines
        (args.flatten).mkString(" || ")
      // Iff (<==>), needs special handling, as this is also represented by "=" internally
      case Eq(lhs, rhs) if lhs.typ == Sort.bool =>
        lines(lhs).mkString + " <==> " + lines(rhs).mkString
      case Eq(lhs, rhs) =>
        lines(lhs).mkString + " == " + lines(rhs).mkString
      case Imp(phi, psi) =>
        psi match {
          case App(inst, args) if args.nonEmpty && inst.toString != "old" =>
            val (assoc_, prec_) = precedence(psi)
            if (prec_ < prec) {
              val con = ("(" +: lines(psi) :+ ")").mkString
              var pre = ""
              phi match {
                case App(inst_, args_) if args_.nonEmpty =>
                  pre = ("(" +: lines(phi) :+ ")").mkString
                case _ =>
                  pre = lines(phi).mkString
              }
              pre + " ==> " + con
            } else {
              lines(phi).mkString + " ==> " + lines(psi).mkString
            }
          case _ if (phi.isInstanceOf[App]) =>
            val App(inst, args) = phi
            if (args.nonEmpty && inst.toString != "old") {
              val (assoc_, prec_) = precedence(phi)
              if (prec_ < prec) {
                val pre = ("(" +: lines(phi) :+ ")").mkString
                val con = lines(psi).mkString
                return pre + " ==> " + con
              }
            }
            lines(phi).mkString + " ==> " + lines(psi).mkString
          case _ =>
            lines(phi).mkString + " ==> " + lines(psi).mkString
        }
      // Infix operators
      case DivBy(lhs, rhs) =>
        lhs match {
          case App(inst_, _) if inst_.toString != "old" =>
            var (assoc_, prec_) = precedence(lhs)
            if (prec_ < prec) {
              val inner = ("(" +: lines(lhs) :+ ")").mkString
              val outer = "/" + lines(rhs).mkString
              inner + " " + outer.mkString(" ")
            } else {
              ((lines(lhs) :+ "/") ++ lines(rhs)).mkString(" ")
            }
          case _ =>
            ((lines(lhs) :+ "/") ++ lines(rhs)).mkString(" ")
        }
      case Mod(lhs, rhs) =>
        lhs match {
          case App(inst_, _) if inst_.toString != "old" =>
            var (assoc_, prec_) = precedence(lhs)
            if (prec_ < prec) {
              val inner = ("(" +: lines(lhs) :+ ")").mkString
              val outer = "%" + lines(rhs).mkString
              inner + " " + outer.mkString(" ")
            } else {
              ((lines(lhs) :+ "%") ++ lines(rhs)).mkString(" ")
            }
          case _ =>
            ((lines(lhs) :+ "%") ++ lines(rhs)).mkString(" ")
        }
      case App(inst, List(left, right))
          if Expr.boogieInfix contains inst.toString =>
        left match {
          case App(inst_, _) if inst_.toString != "old" =>
            var (assoc_, prec_) = precedence(left)
            if (prec_ < prec) {
              val inner = ("(" +: lines(left) :+ ")").mkString
              val outer = inst.toString + lines(right).mkString
              inner + " " + outer.mkString(" ")
            } else {
              ((lines(left) :+ inst.toString) ++ lines(right)).mkString(" ")
            }
          case _ =>
            ((lines(left) :+ inst.toString) ++ lines(right)).mkString(" ")
        }
      // Unary
      case Not(psi) => "!" + psi
      // TODO I have no idea how I am supposed to get the precedence for UMinus
      // since I do not know how to differentiate between "-" infix and "-" prefix
      case UMinus(term) => "-" + term
      case _            => expr.toString
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
    val infix = boogie.Grammar.syntax.infix_ops
    val prefix = boogie.Grammar.syntax.prefix_ops
    val map = boogie.Parser.translate.map(_.swap)

    // TODO: add case when expr is *NOT* an App or not an infix/prefix/postfix operator
    // and return

    val App(inst, args) = expr

    if (infix.contains(inst.toString)) {
      infix.get(inst.toString).get
    } else if (inst.toString == "not") {
      val prec = prefix.get("!").get
      (Non, prec)
    } else if (map.contains(inst.toString)) {
      val Some(op) = map.get(inst.toString)
      infix.get(op).get
    } else {
      (Non, 9)
    }
  }

  private def if_(prog: If): List[String] = {
    val If(test, left, right) = prog
    val first = ("if(" + lines(test).mkString + ") {") +: lines(left)
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

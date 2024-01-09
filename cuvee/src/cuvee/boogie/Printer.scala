package cuvee.boogie

import cuvee.boogie
import cuvee.imp._
import cuvee.pure._
import cuvee.smtlib
import cuvee.smtlib._
import cuvee.util
import cuvee.prove._
import scala.collection.immutable

trait Syntax extends util.Syntax {
  def bexpr: List[Any]
}

/** Printer for boogie format */
object Printer extends cuvee.util.Printer {
  import easyparse.Assoc
  import easyparse.Non

  import boogie.Grammar.syntax
  import boogie.Parser.translate

  // cuvee.name -> (boogie.name, prec, assoc)
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
      key -> (k, v)
    }

  private def lines(cmd: Cmd): List[String] = cmd match {
    case Labels => ???
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
    case Push(depth) => ???
    case Pop(depth)  => ???
    case GetModel    => ???
    case Exit        => ???
    case Reset       => ???
    case Assert(expr) =>
      expr match {
        case Bind(quant, formals, body, _) =>
          List(
            "axiom " + quant.name + " " + vartypes(formals) + " :: ",
            indent(line(body)) + ";"
          )
        case _ =>
          List("axiom " + line(expr) + ";")
      }
    case Lemma(expr, _, _) =>
          List("lemma " + line(expr) + ";")
    case Lemma(expr, tactic, _) =>
      val prop = Prop.from(expr)
      var result: List[String] = Nil

      if (expr.isInstanceOf[Conj])
        result ++= lines(expr)
      else
        result ++= lines(prop)

      if (tactic.nonEmpty)
        result ++= "proof " +: tactic_(tactic.orNull)

      result = indent(result)
      vblock(result)
    case CheckSat                 => ???
    case DeclareSort(name, arity) => List("type " + name + ";")
    case DefineSort(name, _, body) =>
      List("type " + name + " = " + btype(body) + ";")
    case x @ DeclareFun(name, _, _, res) if x.formals.isEmpty =>
      List("const " + name + ": " + btype(res) + ";")
    case x @ DeclareFun(name, params, _, res) =>
      List(
        "function " + name +
          "(" + vartypes(x.formals) + "): " + btype(res) + ";"
      )
    case DefineFun(name, _, formals, res, body, _) =>
      List(
        "function " + name +
          "(" + vartypes(formals) + "): " + btype(res) + " {",
        "  " + line(body),
        "}"
      )
    case DeclareDatatypes(arities, datatypes) =>
      arities zip datatypes map {
        case ((name, arity), Datatype(Nil, constrs)) =>
          val cs = constrs map {
            case (constr, Nil) =>
              constr.name
            case (constr, sels) =>
              val as = sels map { case Fun(name, _, _, res) =>
                name + ": " + btype(res)
              }
              constr.name + as.mkString("(", ", ", ")")
          }
          "data " + name + cs.mkString(" = ", " | ", ";")

        case ((name, arity), Datatype(params, constrs)) =>
          val cs = constrs map {
            case (constr, Nil) =>
              constr.name
            case (constr, sels) =>
              val as = sels map { case Fun(name, _, _, res) =>
                name + ": " + btype(res)
              }
              constr.name + as.mkString("(", ", ", ")")
          }
          "data " + name +
            params.mkString("<", ", ", ">") +
            cs.mkString(" = ", " | ", ";")
      }
    case DeclareProc(name, params, in, out, spec) =>
      var header: String = "procedure " + name
      if (params.nonEmpty) {
        val btypes = params map btype
        header += btypes.mkString("<", ", ", ">")
      }
      if (in.nonEmpty) header += "(" + vartypes(in) + ")"
      else header += "()"

      if (out.nonEmpty)
        header += "returns (" + vartypes(out) + ");"
      else
        header += ";"

      if (spec.nonEmpty)
        header +: bspecs(spec.orNull)
      else
        List(header)
    case DefineProc(name, params, in, out, spec, body) =>
      var header: String = "procedure " + name
      if (params.nonEmpty) {
        val btypes = params map btype
        header += btypes.mkString("<", ", ", ">")
      }
      if (in.nonEmpty) header += "(" + vartypes(in) + ")"
      else header += "()"

      var result: List[String] = List(header)

      if (out.nonEmpty)
        result = result :+ indent("returns (" + vartypes(out) + ")")
      if (spec.nonEmpty)
        result ++= bspecs(spec.orNull)

      result ++= "{" +: lines(body) :+ "}"
      result
  }

  private def lines(prog: Prog): List[String] = prog match {
    case Block(progs) => indent(progs flatMap lines)
    case Break        => List("break;")
    case Return       => List("return;")
    case Local(xs, rhs) =>
      val exprs = for (e <- rhs) yield line(e)
      List("var " + vartypes(xs) + " := " + exprs.mkString(", ") + ";")
    case Assign(xs, rhs) =>
      val exprs = for (e <- rhs) yield line(e)
      List(xs.mkString(",") + " := " + exprs.mkString(",") + ";")
    case Spec(xs, pre, post) =>
      (xs, pre, post) match {
        case (Nil, True, phi) => List("assume " + line(phi) + ";")
        case (Nil, phi, True) => List("assert " + line(phi) + ";")
        case (xs, True, True) => List("havoc " + xs.mkString(", "))
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
      val con = "while(" + line(test) + ")"

      var spec: List[String] = List()
      if (term != Zero)
        spec = spec :+ ("decreases\t" + line(term) + ";")
      if (inv != True)
        spec = spec :+ ("invariant\t" + line(inv) + ";")
      if (sum != True)
        spec = spec :+ ("summary\t" + line(sum) + ";")
      if (!frames.isEmpty) {
        val frames_ = for (f <- frames) yield line(f)
        spec = spec :+ frames_.mkString("frames\t", ",", ";")
      }

      val body_ = "{" +: lines(body) :+ "}"

      (con +: indent(spec)) ++ body_
    case Call(name, in, out) => ???
  }

  /** Takes care of formatting the given argument to print formated boogie.
    *
    * @param any
    *   argument to be formated
    * @return
    *   List[String] to be printed
    */
  def lines(any: Any): List[String] = any match {
    case cmd: Cmd   => lines(cmd) :+ ""
    case prog: Prog => lines(prog)
    case expr: Expr => List(line(expr))
    // Boolean values
    case true  => List("true")
    case false => List("false")
    // Numbers
    case i: Int    => List(i.toString)
    case i: BigInt => List(i.toString)
    case f: Float  => List(f.toString)
    // Name
    case n: util.Name      => List(n.toLabel)
    case smtlib.Error(msg) => List(msg.mkString("\"", " ", "\""))
    case res: Res          => List(res.toString)
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

  private def lines(prop: Prop): List[String] = prop match {
    case Disj(xs, assms, concls) =>
      var result: List[String] = Nil
      val bound =
        for (x <- xs)
          yield x.name.toString + ": " + btype(x.typ)

      val pre =
        for (phi <- assms)
          yield lines(phi)

      val conclst =
        for (phi <- concls)
          yield lines(phi)

      if (bound.nonEmpty)
        result ++= "forall" +: indent(bound)

      if (pre.nonEmpty)
        result ++= "assume" +: indent(pre.flatten)

      if (concls.isEmpty)
        result ++= List("show contradiction")
      else if (concls.size == 1)
        result ++= conclst.flatten
      else if (concls.size > 1)
        result ++= "show one of" +: indent(conclst.flatten)

      result
    case Atom(phi, None)      => List(line(phi))
    case Atom(phi, Some(cex)) => line(phi) :: lines(cex)
  }

  private def lines(conj: Conj): List[String] = {
    val Conj(xs, props) = conj
    var result: List[String] = Nil

    val bound = vartypes(xs)

    val concls = (for (phi <- props) yield lines(phi)).flatten

    if (bound.nonEmpty)
      result ++= indent("exists" :: indent(List(bound)))

    if (props.size == 1)
      result ++= "show" :: indent(concls)
    else if (props.size > 1)
      result ++= "show all of" :: indent(concls)

    result
  }

  private def line(expr: Expr): String = expr match {
    case Lit(any, typ)  => any.toString
    case Var(name, typ) => name.toString
    case App(inst, Nil) => inst.toString
    // Map access
    case Select(arr, idx) =>
      lines(arr).mkString + "[" + lines(idx).mkString + "]"
    case Store(arr, idx, newval) =>
      val assign = (lines(idx) :+ ":=") ++ lines(newval)
      lines(arr).mkString + "[" + assign.mkString(" ") + "]"
    case Ite(test, left, right) =>
      "if(" + line(test) + ") then " + line(left) + " else " + line(right)
    case App(inst, List(left, right)) if infix contains inst.toString =>
      val (name, prec, assoc) = infix(inst.toString)
      var a = line(left)
      var b = line(right)
      // decide if we need parens around a and b
      val (precA, assocA) = precedence(left)
      val (precB, assocB) = precedence(right)

      if (precA < prec || precA == prec && assocA == assoc) a = "(" + a + ")"
      if (precB < prec || precB == prec && assocB == assoc) b = "(" + b + ")"

      a + " " + name + " " + b
    case App(inst, List(expr)) if prefix.contains(inst.toString) =>
      val (name, prec) = prefix(inst.toString)
      val (prec_, assoc) = precedence(expr)

      var arg = line(expr)
      if (prec > prec) arg = "(" + arg + ")"

      name + arg
    case App(inst, args) =>
      val exprs = args map line
      inst.toString + "(" + exprs.mkString(", ") + ")"
    case Bind(quant, formals, body, typ) =>
      val vars = for (x <- formals) yield x + ": " + btype(x.typ)
      val quantifier = quant.toString + " " + vars.mkString(" ") + " :: "
      (quantifier +: lines(body)).mkString
    case Is(arg, fun)            => "is#" + fun.name + "(" + line(arg) + ")"
    case Distinct(exprs)         => ???
    case Let(eqs, body)          => ???
    case Match(expr, cases, typ) => ???
    case Note(expr, attr)        => ???
  }

  private def line(frame: Frame): String = {
    val Frame(array, index, phi) = frame
    array.name + "[" + index.name + "] := " + line(phi)
  }

  private def bspecs(spec: Spec): List[String] = {
    val Spec(xs, pre, post) = spec
    var result: List[String] = Nil

    if (xs.nonEmpty)
      result ++= List("modifies " + vartypes(xs) + ";")
    if (!pre.equals(Nil) && pre != True)
      result ++= List("requires " + line(pre) + ";")
    if (!post.equals(Nil) && post != True)
      result ++= List("ensures " + line(post) + ";")

    indent(result)
  }

  /** Provides a tuple containing precedence and associativity for the given
    * expression.
    *
    * @param expr
    *   to get prec an assoc for
    * @return
    *   prec and assoc for the given expr
    */
  private def precedence(expr: Expr): (Int, Assoc) = expr match {
    case App(inst, _) if infix.contains(inst.toString) =>
      val prec = infix(inst.toString)._2
      val assoc = infix(inst.toString)._3
      (prec, assoc)
    case App(inst, _) if prefix.contains(inst.toString) =>
      val prec = prefix(inst.toString)._2
      (prec, Non)
    case _ => (10, Non)
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

  private def tactic_(t: Tactic): List[String] = t match {
    case Induction(variable, cases) =>
      val header = "induction " + variable.name.toString

      var result: List[String] = Nil
      if (cases.isEmpty) {
        result = List(header)
      } else {
        val body =
          for ((expr, tactic) <- cases)
            yield ("case " + expr.toString + " => ") +: tactic_(tactic)

        result = (header + " {") +: indent(body.flatten) :+ "};"
      }

      indent(result)
    case Show(prop, tactic, cont) =>
      var result: List[String] = Nil
      val head = "show (" + line(prop) + ")"

      if (tactic.nonEmpty)
        result ++= "proof " +: tactic_(tactic.orNull)
      if (cont.nonEmpty)
        result ++= "then " +: tactic_(cont.orNull)

      indent(head +: result)
    case Unfold(target, places, cont) =>
      val (name, num) = target

      var head: String = "unfold " + name
      var result: List[String] = Nil

      if (places.nonEmpty)
        head += " at " + places.orNull.mkString(", ") + " then"

      if (cont.nonEmpty)
        result ++= tactic_(cont.orNull)

      result = head +: result
      indent(result)
    case Auto           => indent(List("auto"))
    case NoAuto(tactic) => indent("no auto " :: tactic_(tactic))
    case Sorry          => indent(List("sorry;"))
  }

  private def vblock(lines: List[String]): List[String] = {
    if (lines.isEmpty)
      return lines

    val head = lines.head.patch(0, "+", 1)
    var result =
      for (line <- lines)
        yield line.patch(0, "|", 1)
    val last = lines.last.patch(0, "+", 1)

    result = result.updated(0, head)
    result = result.updated(result.length - 1, last)

    result
  }

  private def indent(lines: List[String]) = for (l <- lines) yield "  " + l

  private def indent(line: String) = "  " + line

  private def vartypes(vars: List[Var]): String = {
    val vars_ = for (v <- vars) yield v + ": " + btype(v.typ)
    vars_.mkString(", ")
  }

  private def btype(typ: Type): String = typ match {
    case Sort.bool                   => "bool"
    case Sort.int                    => "int"
    case Sort.real                   => "real"
    case Sort(Con.list, List(a))     => btype(a)
    case Sort(Con.array, List(a, b)) => "[" + btype(a) + "]" + btype(b)
    case Param(name)                 => name.toString
    case _                           => typ.toString
  }
}

package cuvee.boogie

import cuvee.boogie
import cuvee.imp._
import cuvee.pure._
import cuvee.smtlib
import cuvee.smtlib._
import cuvee.util
import cuvee.prove._
import cuvee.sexpr

trait Syntax extends util.Syntax {
  def bexpr: List[Any]
}

/** Printer for boogie format */
object Printer extends cuvee.util.Printer {
  import easyparse.Assoc
  import easyparse.Non

  import boogie.Grammar.syntax
  import boogie.Grammar.translate

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
    case Labels =>
      List("get labels;")
    case SetLogic(logic) =>
      List("set logic " + logic + ";")
    case SetOption(attr, arg) =>
      List("set option " + attr + arg + ";")
    case GetInfo(attr) =>
      List("get attribute " + attr + ";")
    case SetInfo(attr, _) =>
      List("set info " + attr + ";")
    case Push(depth) =>
      List("push " + depth + ";")
    case Pop(depth) =>
      List("pop " + depth + ";")
    case GetModel =>
      List("get model;")
    case Exit =>
      List("exit;")
    case Reset =>
      List("reset;")
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
    // Work in progress - print lemmas in cuvee format
    case Lemma(expr, proof, mode, attrs) =>
      var result: List[String] = Nil

      // TODO
      // val label = maybeLabel match {
      //   case Some(l) => s" {:$l}"
      //   case None    => ""
      // }
      val named = for (attr <- attrs.attrs) yield {
        attr match {
          case (kw, None)                 => kw.toString
          case (kw, Some(sexpr.Id(text))) => kw.toString + " \"" + text + "\""
        }
      }

      val named_ =
        if (named.nonEmpty)
          named.mkString(" {", ", ", "}")
        else
          ""

      mode match {
        case Some(Goal) =>
          result = format(s"goal$named_", expr)
        case Some(Free) =>
          result = format(s"free lemma$named_", expr)
        case None =>
          result = format(s"lemma$named_", expr)
      }

      if (proof.nonEmpty) {
        val old = result.last.patch(result.last.length - 1, "", 1)
        result = result.updated(result.length - 1, old)
        result ++= "proof " +: proof_(proof.orNull)

        val last = result.last.patch(result.last.length, ";", 1)
        result = result.updated(result.length - 1, last)
      }

      result
    case CheckSat =>
      List("check sat;")
    case DeclareSort(name, 0) =>
      List("type " + name + ";")
    case DeclareSort(name, arity) =>
      List("type " + name + Type.params("a", arity).mkString("<", ", ", ">") + ";")
    case DefineSort(name, params, body) =>
      List("type " + name + params.mkString("<", ", ", ">") + " = " + btype(body) + ";")
    case DeclareVar(name, typ) =>
      List("var " + name + ": " + btype(typ) + ";")
    case x @ DeclareFun(name, Nil, Nil, res) =>
      List("const " + name + ": " + btype(res) + ";")
    case x @ DeclareFun(name, params, _, res) =>
      List(
        "function " + name + params.mkString("<", ", ", ">") +
          "(" + vartypes(x.formals) + "): " + btype(res) + ";"
      )
    case DefineFun(name, params, formals, res, body, _) =>
      List(
        "function " + name + params.mkString("<", ", ", ">") +
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

    // XXX: refactor with prior case
    case DeclareAbstractions(arities, datatypes) =>
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
          "abstractions " + name + cs.mkString(" = ", " | ", ";")

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
          "abstractions " + name +
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
        header += " returns (" + vartypes(out) + ");"
      else
        header += ";"

      if (spec.nonEmpty)
        header +: bspecs(spec.orNull)
      else
        List(header)

    case DeclareContracts(name, params, formals, contracts) =>
      var header: String = "contract " + name

      if (params.nonEmpty) {
        val btypes = params map btype
        header += btypes.mkString("<", ", ", ">")
      }
      if (formals.nonEmpty) header += "(" + varmodetypes(formals) + ")"
      else header += "()"

      header :: bcontracts(contracts)

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

      result ++= "{" +: block(body) :+ "}"
      result
  }

  private def format(name: String, expr: Expr): List[String] = {
    var phi = formula(expr)
    val head = name + " " + phi.head.trim
    val last = phi.last + ";"

    if (phi.length > 1) {
      phi = phi.updated(0, head)
      phi = phi.updated(phi.length - 1, last)
      head :: phi.tail
    } else {
      List(head + ";")
    }
  }

  private def formula(expr: Expr): List[String] = expr match {
    case And(phis) =>
      val head = formula(phis.head)

      val tail = for (phi <- phis.tail) yield {
        val rest = formula(phi)
        val first = "&& " + rest.head
        first :: rest.tail
      }

      indent(head ++ tail.flatten)
    case Or(phis) =>
      val head = formula(phis.head)

      val tail = for (phi <- phis.tail) yield {
        val rest = formula(phi)
        val first = "|| " + rest.head
        first :: rest.tail
      }

      indent(head ++ tail.flatten)
    case Imp(pre, ant) =>
      val a = formula(pre)
      val a_ = "(" + a.head
      val pre_ = a_ :: a.tail

      val b = formula(ant)
      val b_ = b.last + ")"
      val ant_ = b.updated(b.length - 1, b_)
      // TODO Gidon: Needs one additional space (3 is a horrible number)
      // Where do you want it? Either " ==> " or "==>  "
      val impl = indent(List(" ==> " + ant_.head.trim))
      pre_ ++ impl ++ indent(ant_.tail)
    case Not(Eq(left, right)) =>
      val (name, prec, assoc) = ("!=", 5, easyparse.Left)
      var a = line(left)
      var b = line(right)

      // decide if we need parens around a and b
      val (precA, assocA) = precedence(left)
      val (precB, assocB) = precedence(right)
      if (precA < prec || (precA == prec && assocA != assoc)) a = "(" + a + ")"
      if (precB < prec || (precB == prec && assocB != assoc)) b = "(" + b + ")"

      List(a + " " + name + " " + b)
    case Not(phi) =>
      val phi_ = formula(phi)
      ("!(" + phi_.head) +: phi_.tail :+ ")"
    case Forall(x, phi) =>
      val quant = "(forall " ++ vartypes(x) ++ " ::"
      val phi_ = indent(formula(phi), 3)
      val last = phi_.last + ")"
      quant :: phi_.updated(phi_.length - 1, last)
    case Exists(x, phi) =>
      val quant = "(exists " ++ vartypes(x) ++ " ::"
      val phi_ = indent(formula(phi), 3)
      val last = phi_.last + ")"
      quant :: phi_.updated(phi_.length - 1, last)
    case Post(how, prog, post) =>
      val as = lines(prog)
      val bs = lines(post)
      val (lp, rp) = modality(how)
      List(lp) ++ indent(as) ++ List(rp + "(") ++ indent(bs) ++ List(")")
    case _ =>
      List(line(expr))
  }

  private def lines(prog: Prog): List[String] = prog match {
    case Block(progs) => "{" +: indent(progs flatMap lines) :+ "}"
    case Break        => List("break;")
    case Return       => List("return;")
    case Continue     => List("continue;")
    case Local(xs, Nil) =>
      List("var " + vartypes(xs) + ";")
    case Local(xs, rhs) =>
      val exprs = for (e <- rhs) yield line(e)
      List("var " + vartypes(xs) + " := " + exprs.mkString(", ") + ";")
    case Assign(xs, rhs) =>
      val pairs = for ((l, r) <- xs zip rhs) yield Assign.flatten(l, r)
      val (lhs_, rhs_) = pairs.unzip
      val exprs = for (e <- rhs_) yield line(e)
      List(lhs_.mkString(", ") + " := " + exprs.mkString(", ") + ";")
    case Spec(Nil, True, phi) =>
      List("assume " + line(phi) + ";")
    case Spec(Nil, phi, True) =>
      List("assert " + line(phi) + ";")
    case Spec(xs, True, True) =>
      List("havoc " + xs.mkString(", ") + ";")
    case Spec(xs, pre, post) =>
      List(
        "transition " + xs.mkString(", ") + " :: " + line(pre) + " | " + line(
          post
        ) + ";"
      )
    case x @ If(test, left, right) => if_(x)
    case While(test, body, term, inv, sum, frames) =>
      val first = "while(" + line(test) + ")"

      var spec: List[String] = List()
      if (term != Zero)
        spec ++= format("decreases", term)
      if (inv != True)
        spec ++= format("invariant", inv)
      if (sum != True)
        spec ++= format("summary", cuvee.boogie.Parser.old_to_final(sum))
      if (!frames.isEmpty) {
        ???
        // val frames_ = for (f <- frames) yield line(f)
        // spec ++= frames_.mkString("frames\t", ",", ";")
      }

      if (spec.isEmpty) {
        val body_ = block(body) :+ "}"
        (first + " {") +: body_
      } else {
        val body_ = "{" +: block(body) :+ "}"
        (first +: indent(spec)) ++ body_
      }
    case Call(name, in, out) =>
      val args = for (e <- in) yield line(e)
      List(
        out.mkString(", ") + " := call " + name + "(" + args.mkString(
          ", "
        ) + ");"
      )
  }

  def block(prog: Prog) =
    prog match {
      case Block(progs) =>
        indent(progs flatMap lines)
      case _ =>
        indent(lines(prog))
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

    case smtlib.Error(info) => lines("error: " + info.mkString(" "))

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
    case Not(Eq(left, right)) =>
      val (name, prec, assoc) = ("!=", 5, easyparse.Left)
      var a = line(left)
      var b = line(right)

      // decide if we need parens around a and b
      val (precA, assocA) = precedence(left)
      val (precB, assocB) = precedence(right)
      if (precA < prec || (precA == prec && assocA != assoc)) a = "(" + a + ")"
      if (precB < prec || (precB == prec && assocB != assoc)) b = "(" + b + ")"

      a + " " + name + " " + b
    case App(inst, List(left, right)) if infix contains inst.toString =>
      val (name, prec, assoc) = infix(inst.toString)
      var a = line(left)
      var b = line(right)
      // decide if we need parens around a and b
      val (precA, assocA) = precedence(left)
      val (precB, assocB) = precedence(right)

      /* Parens are needed if the precedence of the child (precA, precB) is
       * smaller than that of the current node (prec).
       * In theory they are also needed if the precedence of both is the same
       * but the associativity divers.*/
      if (precA < prec || (precA == prec && assocA != assoc)) a = "(" + a + ")"
      if (precB < prec || (precB == prec && assocB != assoc)) b = "(" + b + ")"

      a + " " + name + " " + b
    case Not(phi) =>
      val phi_ = line(phi)
      "!(" + phi_ + ")"
    case App(inst, List(expr)) if prefix.contains(inst.toString) =>
      val (name, prec) = prefix(inst.toString)
      val (prec_, assoc) = precedence(expr)

      var arg = line(expr)
      if (prec > prec_) arg = "(" + arg + ")"

      name + arg
    case App(inst, args) =>
      val exprs = args map line
      inst.toString + "(" + exprs.mkString(", ") + ")"
    case At(where, arg) =>
      where + "(" + arg + ")"
    case Bind(quant, formals, body, typ) =>
      val vars = for (x <- formals) yield x + ": " + btype(x.typ)
      val quantifier = quant.toString + vars.mkString(" ", ", ", " :: ")
      quantifier + line(body)
    case Is(arg, fun) =>
      "is#" + fun.name + "(" + line(arg) + ")"
    case Distinct(exprs) =>
      "distinct " + lines(exprs) + ";" // TODO: fix and test
    case Let(eqs, body) =>
      "let " + lines(eqs) + lines(body) + ";" // TODO: fix and test
    case Match(expr, cases, typ) =>
      // TODO solution for cases in method
      "match " + line(expr) + cases.toString + btype(
        typ
      ) + ";" // TODO: fix and test
    case note @ cuvee.pure.Note(expr, attrs) =>
      attrs.flatten.mkString("{", ", ", "} ") + line(expr)

    case extra: Extra =>
      extra.toString
  }

  private def modality(how: Modality) = how match {
    case WP  => ("{", "}")
    case Box => ("[", "]")
    case Dia => ("<", ">")
  }

  private def line(frame: Frame): String = {
    val Frame(array, index, phi) = frame
    array.name + "[" + index.name + "] := " + line(phi)
  }

  private def bspecs(spec: Spec): List[String] = {
    val Spec(xs, pre, post) = spec
    var result: List[String] = Nil

    if (xs.nonEmpty)
      result ++= List("modifies " + xs.mkString(", ") + ";")
    if (!pre.equals(Nil) && pre != True)
      result ++= format("requires", pre)
    if (!post.equals(Nil) && post != True)
      result ++= format("ensures ", post)

    indent(result)
  }

  private def bcontracts(contracts: List[(Expr, Expr)]): List[String] = contracts match {
    case Nil =>
      Nil

    case (pre, post) :: rest =>
      val pres = And.flattenStrong(pre)
      val posts = And.flattenStrong(post)

      val pre_ = pres flatMap (format("requires", _))
      val post_ = posts flatMap (format("ensures ", _))

      val here = indent(pre_ ++ post_)
      val there = bcontracts(rest)

      if (rest.isEmpty)
        here
      else
        here ++ List("also") ++ there
  }

  /** Provides a tuple containing precedence and associativity for the given expression.
    *
    * @param expr
    *   to get prec and assoc for
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
    case Bind(_, _, _, _) =>
      (0, Non)
    case _ =>
      (10, Non)
  }

  private def if_(prog: If): List[String] = {
    val If(test, left, right) = prog
    val first = ("if(" + lines(test).mkString + ") {") +: block(left)

    right match {
      case right @ If(test_, left_, right_) =>
        val (second :: rest) = if_(right)
        (first :+ "} else " + second) ++ rest
      case Block(Nil) =>
        first :+ "}"
      case _ =>
        (first :+ "} else {") ++ (block(right) :+ "}")
      // case _ =>
      //   first :+ ("// Unknown operation in If: " ++ right.toString)
    }
  }

  def proof(p: Proof): String = {
    var result: String = ""
    for(line <- proof_(p)) 
      result += line ++ "\n"
    result 
  }


  private def proof_(p: Proof): List[String] = p match {
    case Proof(Induction(variable), subproofs) => 
      val header = "induction " + variable.name.toString

      var result: List[String] = Nil
      if (subproofs.isEmpty) {
        result = List(header)
      } else {
        val body = for ((sel, subproof) <- subproofs) 
          yield sel.toString() +: proof_(subproof)
        result = (header + " {") +: indent(body.flatten) :+ "}"
      }

      indent(result)

    case Proof(Show(expr), subproofs) => 
      var result: List[String] = Nil
      val head = "show (" + line(expr) + ")"

      val cont = subproofs map {
        case (sel, proof) => sel.toString +: proof_(proof)
      }

      indent(head +: indent(cont.flatten))

    case Proof(Unfold(target, places), subproofs) => 
      val (name, num) = target

      var head: String = "unfold " + name
      var result: List[String] = Nil

      if (places.nonEmpty)
        head += " at " + places.orNull.mkString(", ")

      assert(subproofs.length <= 1)
      if (subproofs.nonEmpty){
        val (sel, subproof) = subproofs.head
        result ++= sel.toString +: proof_(subproof)
      }

      result = head +: result
      indent(result)

    case Proof(Sorry, _)      => indent(List("sorry"))
    case Proof(Auto, _)       => indent(List("auto"))
    case Proof(BreakPoint, _) => indent(List("break"))
  }

  private def indent(lines: List[String], times: Int = 1) =
    for (l <- lines) yield ("  " * times) + l

  private def indent(line: String) = "  " + line

  private def vartypes(vars: List[Var]): String = {
    val vars_ = for (v <- vars) yield v + ": " + btype(v.typ)
    vars_.mkString(", ")
  }

  private def varmodetypes(vars: List[(cuvee.imp.Mode, Var)]): String = {
    val vars_ = for ((m, v) <- vars) yield v + ": " + m + " " + btype(v.typ)
    vars_.mkString(", ")
  }

  private def btype(typ: Type): String = typ match {
    case Param(name) => name.toString
    case Sort.bool   => "bool"
    case Sort.int    => "int"
    case Sort.real   => "real"

    case Sort(Con.array, List(a, b)) =>
      "[" + btype(a) + "]" + btype(b)

    case Sort(con, Nil) =>
      con.name.toString()

    case Sort(con, args) =>
      val args_ = args map btype
      con.name.toString() + args_.mkString("<", ",", ">")
  }
}

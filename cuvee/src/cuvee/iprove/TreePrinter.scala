package cuvee.iprove

import cuvee.boogie
import cuvee.imp._
import cuvee.pure._
import cuvee.smtlib
import cuvee.util
import cuvee.sexpr
import io.AnsiColor._
import cuvee.boogie.Syntax
import scala.io.AnsiColor
import java.util.regex.Pattern.quote
import cuvee.iprove
import cuvee.State
import cuvee.prove

/** Printer for boogie format */
object TreePrinter extends cuvee.util.Printer {
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
    case prog: Prog => lines(prog)
    case expr: Expr => List(line(expr))
    case tree: Tree => lines(tree)
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
    case res: smtlib.Res          => List(res.toString)
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
    case note@cuvee.pure.Note(expr, attr) =>
      note.flatAttr.mkString("{", ", ", "} ") + line(expr)
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
      result ++= format("ensures", post)

    indent(result)
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

  def tactic_(t: cuvee.prove.Tactic): List[String] =  t match {
      case prove.Induction(variable) =>
        val header = "induction " + variable.name.toString
  
        var result: List[String] = Nil
        val cases: List[(Expr, prove.Tactic)] = Nil
        if (cases.isEmpty) {
          result = List(header)
        } else {
          val body =
            for ((expr, tactic) <- cases)
              yield ("case " + expr.toString + " => ") +: tactic_(tactic)
  
          result = (header + " {") +: indent(body.flatten) :+ "}"
        }
  
        indent(result)

      case prove.Show(prop) =>
        var result: List[String] = Nil
        val head = "show (" + line(prop) + ")"
  
        // if (tactic.nonEmpty)
        //   result ++= "proof " +: tactic_(tactic.orNull)
        // if (cont.nonEmpty)
        //   result ++= "then " +: tactic_(cont.orNull)
  
        indent(head +: result)
      case prove.Unfold(target, places) =>
        val (name, num) = target
  
        var head: String = "unfold " + name
        var result: List[String] = Nil
  
        if (places.nonEmpty)
          head += " at " + places.orNull.mkString(", ") + " then"
  
        //if (cont.nonEmpty)
          //result ++= tactic_(cont.orNull)
  
        result = head +: result
        indent(result)
      case prove.Auto           => indent(List("auto"))
      case prove.NoAuto         => indent(List("noauto "))//:: tactic_(proof.tactic))
      case prove.Sorry          => indent(List("sorry"))
    }
  
    

  val keywords = Map(
    //keywords
    "proof" -> BLUE,
    "then" -> BLUE,
    "lemma" -> BLUE,
    "case" -> BLUE,
    "first" -> BLUE,
    "goal" -> BLUE,
    "assms" -> BLUE,
    "vars" -> BLUE,
    "tactic" -> BLUE,
    //tactics
    "show" -> YELLOW,
    "auto" -> YELLOW,
    "induction" -> YELLOW,
    "cases" -> YELLOW,
    "split" -> YELLOW,
    "simplify" -> YELLOW,
    "skip" -> YELLOW,
    "sorry" -> YELLOW,
    "open" -> YELLOW,
    "up" -> YELLOW,
    "down" -> YELLOW,
    "undo" -> YELLOW,
    "redo" -> YELLOW,
    "exit" -> YELLOW,
    //"bad"
    "false" -> RED,
    "open goal" -> RED,
    //"good"
    "true" -> GREEN
  )
  val grey = "\u001B[90m"
  val lila = "\u001B[35m"
  val yellow = AnsiColor.YELLOW
  val highlight = yellow


  private def colorKeywords(string: String): String = {
     // Go through each keyword and replace it with the colored version
      keywords.foldLeft(string) ( 
        (text, map) => {
          val (keyword, color) = map 
          val keywordPattern = ("("+keyword+")\\b").r
          keywordPattern.replaceAllIn(text, s"${color}${keyword}${RESET}")
        }
      )
  }

  def formatTactic(tactic: Option[Tactic], color: Boolean = true): String = tactic match{
    case None => "none"
    case Some(value) =>{ val result = value match{
        case Auto(prover) => "auto" //+ prover.toString()
        case Split => "split"
        case Induction(variable, true) => "induction " + variable
        case Induction(variable, false) => "cases " + variable
        case Show(expr) => "show " + expr
        case Sorry => "sorry"
        case iprove.Skip => "skip"
        case iprove.Simplify => "simplify"
        case Default(tactic) => "default " + formatTactic(Some(tactic), false)
        //navigation
        case Exit => "exit"
        case Help => "help"
        case Redo => "redo"
        case SelectChild(_) => "down"
        case SelectGoal(_) => "open"
        case Undo(true) => "undo here"
        case Undo(false) => "undo"
        case Up => "up"
        case _ => "???"
      }
      if(color) colorKeywords("tactic: " + result) else result
    }
  }


  def formatProveTactic(tactic: prove.Tactic): String = tactic match {
    case prove.Auto => "auto"
    case prove.Induction(variable) => "induction " + variable
    case prove.Show(expr) => "show " + expr
    case prove.Sorry => "sorry"
    //case prove.Skip | _ => "skip"
  }

  //format Prop Object into local context String
  def formatProp(expr: Expr): String = {
    val result = expr match{
      case _ if(expr.isAtomic) => "goal: " + expr
      case Clause(xs, assms, concl) => (xs, assms) match{
        case (Nil, Nil) => "goal: " + concl
        case (Nil, _)   => "assms: " + (assms).mkString(",\n" + " " * 7) + "\ngoal: " + concl
        case (_, Nil)   => "vars: " + vartypes(xs) + "\ngoal: " + concl
        case _          => "vars: " + vartypes(xs) +  "\nassms: " +  
          (assms).mkString(",\n" + " " * 7) + "\ngoal: "  + concl
        }
    }
    colorKeywords(result)
  }

  /**
    * each step shows either:
    * The (sub-)goal and list of attempts (marked with *) - if this goal is at the current position. 
    * The (sub-)goal and a number of attempts - if this subgoal is an open leaf.
    * The applied tactic and a number of attempts - if this subgoal has an applied tactic that is not "skip".
    * If a leaf goal is closed it has no further subgoals and while not at that goal shows the successful tactic (only possible with "auto", "simplify", "sorry")
    * 
    * @param tree the Tree Object containing all subgoals and tactic attempts
    * @param position the name of the current goal
    * @param indent String to indent the children correctly
    * @return a String representing the proof Tree
    * 
    */ 
  def treeView(tree: Tree, position: String, indent: String = ""): String = {
    var newIndent = indent + "  "
    val result : String = tree match{
      case Step(goal, Nil, name, index) => {
        //goal is open - no attempts
        formatGoal(tree, position)  + "\n"
      }
      case Step(goal, attempts, name, index) => {
        val attempt = attempts(index)
        val prems = attempt.prems
        val isCurrent: Boolean = tree.name == position
        var temp = if(isCurrent) formatGoal(tree, position) + attemptsList(attempts, index, isCurrent, indent) + "\n"
                  else tacticFormatting(attempt.tactic) + attemptsList(attempts, index, false, indent) + "\n" 
        prems match{
          // no subgoals
          case Nil => attempt.tactic match{ 
            //closed 
            case Auto(_) | iprove.Simplify | Sorry if(!isCurrent) =>  
              s"${AnsiColor.GREEN}" + tacticFormatting(attempt.tactic, isCurrent) + " □" + s"${AnsiColor.RESET}" +  
              attemptsList(attempts, index, isCurrent, indent) + "\n" 
            //open - goal is shown + if showing the current position extensive attemptslist, else number of further attempts
            case _ =>  formatGoal(tree, position) + attemptsList(attempts, index, isCurrent, indent) + "\n"
          }
          // one subgoal
          case head :: Nil => temp + newIndent + "|____" + treeView(head, position, newIndent + "    ") 
          // multiple subgoals
          case head :: tail => {
            val last = prems(prems.length - 1)
            val premWitoutLast = prems.removed(prems.length - 1)
            temp += premWitoutLast.map(prem => newIndent + "|____" + treeView(prem, position, newIndent + "|    ")).mkString
            temp + newIndent + "|____" + treeView(last, position, newIndent + "    ")
          }
        }
      }
    }
    result
  }

  //get String of proof Tactic name
  def tacticFormatting(tactic: Tactic, color: Boolean = false): String = {
    val result = tactic match{
        case Auto(prover) => "auto" //+ prover.toString()
        case Split => "split"
        case Induction(variable, true) => "induction " + variable
        case Induction(variable, false) => "cases " + variable
        case Show(prop) => "show"
        case Sorry => "sorry"
        case iprove.Skip => "_"
        case iprove.Simplify => "simplify"
        case Default(tactic) => tacticFormatting(tactic, color)
        case _ => "navigation ?"
    }
    if(color) s"${highlight}${result}${AnsiColor.RESET}" else result
  }

  private def formatGoal(step: Tree, index: String): String = {
    val goal : String = step.goal.toString()
    if(index == step.name) s"${highlight}${goal + "*"}${AnsiColor.RESET}"
    else goal
  }

  //format List of Attempts according to position (extensive: [tactic1, tactic2*] / not: (+n))
  private def attemptsList(attempts: List[Attempt], index: Int, extensive: Boolean = false, indent: String): String = {
    if(extensive) 
      "\n" + indent + s"${grey}[" + 
      attempts.zipWithIndex.map{case (attempt, i) => 
          if(i == index) s"${highlight}" + tacticFormatting(attempt.tactic) + "*" + s"${grey}"
          else tacticFormatting(attempt.tactic) }.mkString(", ") + 
        s"]${AnsiColor.RESET}"
    
    else if(attempts.length > 1) /*"\n" + indent +*/ s"${grey} (+ " + (attempts.length - 1) +s")${AnsiColor.RESET}" 
    else ""
  }

  //get representation of proof in boogie Format from Tree Object
  def proofString(tree: Tree, state: State, color: Boolean): String = { 
    val lemma = "lemma " ++ line(tree.goal) + "\nproof"
    var tactic = lemma :: proofString(tree, state)

    var res: String = ""
    for (line <- tactic) res = res ++ "\n" + line
    if(color) {res = colorKeywords(res)}
    res ++ ";\n"
  }

  private def proofString(tree: Tree, state: State): List[String] = tree match {
    case Step(goal, Nil, name, index) => indent(List("skip"))
    case Step(goal, attempts, name, index) => {
      val attempt = attempts(index)
      tactics(attempt.tactic, attempt.prems, state)
    }
  }

  private def tactics(t: Tactic, subtree: List[Tree], state: State): List[String] = t match {
    case Induction(variable, hyp) =>
      val header = if(hyp) "induction " + variable else "//cases " + variable
      var result: List[String] = Nil
      
      val sort = variable.typ.asInstanceOf[Sort]
      val dt = state.datatypes
      .get(sort.con.name)
      .getOrElse(
        throw new TacticNotApplicableException(
          f"Can't apply induction to variable $variable, as it has no associated data type"
        )
      )

      val cases = dt.constrs
      //for(case_ <- cases) {print(getConstrCase(case_._1, case_._2))}
      assert(subtree.length == cases.length)

      val body =
        for ((tree, case_) <- subtree.zip(cases))
          yield ("case " + getConstrCase(case_._1, case_._2) + " => ") +: proofString(tree, state)

      result = (header + " {") +: indent(body.flatten) :+ (if(hyp) "}" else "//}")
      indent(result)

    case Show(prop) => 
      val head = "show (" + line(prop) + ")"
      var result = "proof " +: proofString(subtree(0), state)
      result ++= "then " +: proofString(subtree(1), state)
      
      indent(head +: indent(result))
    
    case Auto(_) =>  subtree match{
      case Nil => indent(List("auto"))
      case head :: Nil => indent("auto " +: proofString(head, state))
      case head :: next => ??? 
    }
    case Sorry => indent(List("sorry"))
    case iprove.Skip => indent(List("skip"))
    case iprove.Simplify => " //simplify" +: proofString(subtree(0), state)
    case Split => 
      val body =
        for (((tree), i) <- subtree.zipWithIndex)
          yield ("case " + i + " => ") +: proofString(tree, state) 
      "//split" +: indent(body.flatten)
    
    case _ => Nil
  }

  //Tree object to Json String
  def getTreeJSON(tree: Tree, i: Int = 1): String = {
    val result: String = tree match {
       case Step(goal, Nil, name, index) => indent(
        ("\"name\": \"" + name + "\"") ::
        ("\"goal\": \"" + goal + "\"") ::
        ("\"index\":" + "\"" + index + "\"") ::
        ("\"attempts\": []") :: Nil, i)
        .mkString(("  " * (i-1)) +"{\n", ",\n",  "\n" + (("  " * (i-1)) + "}"))
       case Step(goal, attempts, name, index) => indent(
        ("\"name\": \"" + name + "\"") :: 
        ("\"goal\": \"" + goal + "\"") ::
        ("\"index\":" + "\"" + index + "\"") ::
        ("\"attempts\": [\n" + attempts.map(attempt => getAttemptJSON(attempt, i + 1))
            .mkString(",\n")) + "]" :: Nil, i)
        .mkString(("  " * (i-1)) +"{\n", ",\n", "\n" + (("  " * (i-1)) + "}"))
    }
    result
  }

  private def getAttemptJSON(attempt: Attempt, i: Int = 1): String = attempt match{
    case Attempt(tactic, Nil) => indent(
      "\"tactic\": \"" + formatTactic(Some(tactic),false) + "\""::
      "\"subgoals\": []" :: Nil, i)
      .mkString(("  " * (i-1)) + "{\n", ",\n",  "\n" + (("  " * (i-1)) + "}"))
    
    case Attempt(tactic, prems) => indent(
      "\"tactic\": \"" + formatTactic(Some(tactic), false) + "\"" ::
      "\"subgoals\": [\n" + prems.map(prem => getTreeJSON(prem, i + 1)).mkString(",\n") + "]"
      :: Nil, i)
      .mkString(("  " * (i-1)) + "{\n", ",\n",  "\n" + (("  " * (i-1)) + "}"))
  }


  private def getConstrCase(fun: Fun, args: List[Fun]): String = {
    args match{
      case Nil => fun.name.name
      case head :: Nil => fun.name.name + "(" + head.name + ")"
      case head :: next => fun.name.name + "(" + args.map(arg => arg.name).mkString(", ") + ")"
    }
  }

  private def indent(lines: List[String], times: Int = 1) =
    for (l <- lines) yield ("  " * times) + l

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

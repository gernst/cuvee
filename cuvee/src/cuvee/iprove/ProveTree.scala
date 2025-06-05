package cuvee.iprove

import cuvee.pure._
import cuvee.pipe.Stage
import cuvee.prove.Prover
import cuvee.prove
import cuvee.util.Name
import cuvee.State

import cuvee.smtlib.Cmd
import cuvee.smtlib.Assert
import cuvee.smtlib.Solver
import cuvee.smtlib.Free
import cuvee.smtlib.DeclareVar
import cuvee.smtlib.Goal
import cuvee.smtlib.Lemma

import java.io.StringReader
import java.io.BufferedReader
import java.io.Reader
import java.io.PrintWriter
import java.io.File
import java.io.FileNotFoundException
import java.io.FileWriter
import scala.io._
import scala.io.StdIn._
import scala.util.matching.Regex
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.text.ParseException
import java.text.SimpleDateFormat
import cuvee.boogie.Parser
import cuvee.boogie.Grammar


class ProveTree(
  prover: Prover,
  simplify: Boolean,
  rewrite: Boolean,
  proveNegatedAsserts: Boolean,
  crosscheckProver: Boolean,
  debug: Boolean,
  sessionFile: Option[String],
  auto: Boolean
) extends Stage {  
  val defaultIP: Tactic = if(auto) Auto(prover) else Skip
  val defaultP: prove.Proof = prove.Proof(prove.Auto, Nil)//TODO restore if(auto) prove.Auto else prove.Skip
  
  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) = {
    val results = exec(prefix, cmds, state)
    prover.exec(last, state)
    results
  }

  def exec(prefix: List[Cmd], cmds: List[Cmd], state: State) = {
    Rules.ite = false
    Rules.shortcut = false
    val rws: Map[Fun, List[Rule]] = {
      val rules = Rewrite.from(prefix ++ cmds, state) // add some new rewrite rules
      rules.groupBy(_.fun) // update rule index
    } 


    cmds flatMap {
      case cmd @ Lemma(expr, tactic, Some(Free), label) =>
          prover.exec(cmd, state)
          List(cmd)

      case cmd @ Lemma(expr, tactic, Some(Goal), label) =>
        val proofTree: Tree = repl(expr, tactic, state, rws, sessionFile)
        for (goal_ <- proofTree.results if !goal_.equals(True))
        yield {
          val expr_ = goal_
          Lemma(expr_, None, Some(Goal), label)
        } //yields list of subexpressions//

      case cmd @ Lemma(expr, tactic, None, label) =>
        val proofTree: Tree = repl(expr, tactic, state, rws, sessionFile)
        if(!proofTree.isClosed){
          List(Lemma(expr, None, None, label))
        }
        else
          List(Lemma(expr, None, Some(Free), label))
        
      case cmd @ Assert(Not(App(Inst(fun, _), _)))
        if proveNegatedAsserts && (rws contains fun) && rws(fun).nonEmpty =>
          prover.exec(cmd, state)
          List(cmd)

      case cmd @ Assert(Not(expr)) if proveNegatedAsserts =>
        val proofTree = repl(expr, Some(prove.Proof(prove.Auto, Nil)), state, rws, sessionFile)
        for (goal_ <- proofTree.results)
        yield {
          Assert(Simplify.not(goal_))
        }

      case cmd: DeclareVar =>
        List(cmd)

      case cmd =>
        prover.exec(cmd, state)
        List(cmd)
    }
  }

  /**
    * Processes the user commands in a repl loop. User inputs a tactic which gets parsed to a tactic. 
    * The Tactic is evaluated and the users view is updated.  
    * Keeps track of a Tree Object which stores proof attempts and subgoals. 
    * A pointer to the id of the current subgoal is kept.
    *
    * @param expr the overall proof goal / lemma 
    * @param tactic the nested proof tactics extracted from the proof file
    * @param state 
    * @param rws the rewrite rules
    * @param sessionPath optional path to a (input/output) session file
    * @return the tree object when the interactive session was exited
    */
  def repl(expr: Expr, tactic: Option[prove.Proof], state: State, rws: Map[Fun, List[Rule]], sessionPath: Option[String]): Tree = {
    var currentTactic: Tactic = Skip
    var exit: Boolean = false
    var message = ""
    var proofTree : Tree = Step(expr, Nil, "0")
    val seperator = " : "
    val sessionStart =  ("goal" + seperator + expr.toString())

    /** 
     * evaluates Tactic (reconstruct tree with new goals / navigate)
     * applies @tactic to @goal at position @index in proofTree
     * @return index, goal of new position in Tree, feedback from applied tactic
     */
    def step(goal: Expr, tactic: Tactic, state: State, index: String): (String, Expr, String) = tactic match{
      case Help => 
        val helpMessage = 
          "\nproof tactics: " +
            "'induction' variable, 'cases' variable, 'show' expression, 'split', 'auto', 'sorry', 'simplify', 'default' tactic" +
          "\nnavigation: 'skip', 'open' [n], 'up', 'down' [n]" + 
          "\nattempt management: 'undo' [here] and 'redo'" +
          "\n'exit': exit the proof for the current lemma / goal" +
          "\n'rules': get a list of the rewrite / simplification rules" +
          "\n'proof': get the current proof tree as a boogie proof" +
          "\n'help': this message" +
          "\nsee iprove/README.md for a more detailed explanation of the tactics"
        (index, goal, helpMessage)

      case Proof =>
        val proof =  TreePrinter.proofString(proofTree, state, true)
        (index, goal, proof)

      case Check => 
        val check = "\nproofTree is closed: " + proofTree.isClosed
        (index, goal, check)

      case Skip => 
        val (newIndex, goal) = nextOpenGoal(index, proofTree)
        (newIndex, goal, "")
  
      case Exit => 
        val exitMessage = "goal has been proven: " + proofTree.isClosed
        exit = true
        (index, goal, exitMessage)

      case RwRules => 
        val message = "rewrite rules: \n" + rws.map{case (fun, lst) => fun + "\n" + " " * 4 + lst.mkString("\n" + " " * 4)}.mkString("\n")
        (index, goal, message) 

      case cuvee.iprove.Goal => 
        val message = "full goal: " + goal
        (index, goal, message)
      
  
      case SelectGoal(number) => 
        val openGoals: List[(String, Expr)] = proofTree.getOpen
        
        //check if there are open goals left
        var nr: Int = openGoals.length match{
          case 0 => return (index, goal, "")
          case 1 => 0
          case _ if(0 <= number && number < openGoals.length) => number
          case _ => openGoals.zipWithIndex foreach {
                    case ((name, goal), i) => println(i + ": " + goal)} 
                    -1
        } 
        //user selection 
        while(!(0 <= nr && nr < openGoals.length)){
          try {
            print("continue at nr.: ")
            nr = readInt()
          } catch {
              case e: NumberFormatException => nr -1
          }
        }
        val (index_, goal_) = openGoals(nr)
        (index_, goal_, "")
        

      case Up => 
        val parent = proofTree.getParent(index)
        val (parentIndex, parentGoal) = parent match {
          case None => (index, goal)
          case Some(parent) => parent
        }
        (parentIndex, parentGoal, "")
      

      case SelectChild(number) => 
        val children: List[(String, Expr)] = proofTree.getChildrenAt(index)
        
        var childNr: Int = children.length match{
          case 0 => {
            return (index, goal, "")
          }
          case 1 => 0
          case _ if (0 <= number && number < children.length) => number
          case _ => {
            children.zipWithIndex foreach {case ((name, goal), i) => 
              println(i + ": " + goal)}
            -1
          }
        } 
        //user selection 
        while(!(0 <= childNr && childNr < children.length)){
          try {
            print("continue at child nr.: ")
            childNr = readInt()
          } catch {
              case e: NumberFormatException => childNr -1
          }
        }
        val (index_, newGoal) = children(childNr)
        (index_, newGoal, "")


      case Undo(local) =>
        if(!local) { 
          val (index_, goal_, message) = step(goal, Up, state, index)
          proofTree = proofTree.undo(index_)
          return (index_, goal_, "to restore tactic type 'redo'")
        }
        else {
          proofTree = proofTree.undo(index)
          (index, goal, "to restore tactic type 'redo'")
        }

      case Redo =>
        proofTree = proofTree.redo(index)
        val restoredTactic = proofTree.getTactic(index)
        val message = if(restoredTactic.isDefined) "restored " + TreePrinter.tacticFormatting(restoredTactic.get)
                      else "restored: _"
        (index, goal, message)
      
      case Default(defaultTactic) => 
        val openGoals = proofTree.getOpen
        openGoals map {case (name, goal) => step(goal, defaultTactic, state, name)}
        (index, goal, "applied " + TreePrinter.formatTactic(Some(defaultTactic), false) + " to all open goals")

      //proof tactics
      case _ => 
        if(viewMode(proofTree, index)){
          (index, goal, "apply 'undo here' to retry tactic")
        } 
        else{ 
          try{
            val subgoals = tactic.apply(goal, state, rws)
            val subtrees = subgoals.map{
              case (subgoal, name) => Step(subgoal, Nil, (index + name))
            }
            proofTree = proofTree.newAttempt(index, subtrees, tactic)
            
            if(subtrees.length == 0){
              val (newIndex, goal) = nextOpenGoal(index, proofTree)
              (newIndex, goal, "(sub)goal was closed")
            }
            else {
              var message = subtrees.length + " new goal(s)"
              if(subgoals.length > 1) subgoals.map{case (goal_, name_) => {
                val (_, _, mssg) = step(goal_, defaultIP, state, index + name_)
                message += "\n" + mssg
              }}
              val open = proofTree.getOpenAt(index)
              val (newIndex, goal) = if(!open.isEmpty) open.head else ("0", proofTree.goal)
              (newIndex, goal, message)
            }
          }
          catch{
            case e: Throwable => (index, goal, "error while applying tactic: " + e )
          }
        }
    }
    
    /**
     * restores the proof Tree Data Structure from the Session file if available, else restoreProof() is called
     * to restore the Tree from the proof File  
     *
     * @param expr the overall goal of the current proof 
     * @param tactic optional Tactic from input file
     * @param rws rewrite rules
     * @param sessionPath given path for session input
     * @return the reconstructed Tree Structure, the File Object for session output
     */
    def restoreSession(expr: Expr, tactic: Option[prove.Proof], state: State, rws: Map[Fun, List[Rule]], sessionPath: Option[String]): (Tree, File) = {
      var session: List[String] = Nil
      var rest: List[String] = Nil
      val datePattern = "yyyy-MM-dd_HH:mm"
      val dtFormatter = DateTimeFormatter.ofPattern(datePattern)
      
      println("\u001b[2J\u001B[0;0H")
      println("session file: " + sessionPath.getOrElse(""))
 
      val sessionFile : File = sessionPath match {
        case None => {
          val file = new File("temp.txt")
          val fw = new FileWriter(file , true)
          fw.write("\n" + sessionStart)
          fw.write("\n" + dtFormatter.format(LocalDateTime.now))
          fw.close()
          file
        }
        case Some(path) => {
          val file = new File(path)
          try{
            var found = false 
            var endSearch = false
            val bsrc = Source.fromFile(file)
            bsrc.getLines().foreach{ 
              line => 
                if(line.isBlank())()
                else if(found && line.contains("goal" + seperator)){ //start of next session
                  rest = rest :+ line
                  found = false
                  endSearch = true
                }
                else if(!endSearch && line == sessionStart)
                  found = true
                else if(found && isTimestamp(line, datePattern))
                  println(line)
                else if(!endSearch && found)
                  session = session :+ line
                else
                  rest = rest :+ line
            }
            bsrc.close()
          } catch {
            case e: Throwable => println(e.getMessage + " while restoring session")
          }
          val startOfFile: Int = path.lastIndexOf("/")
          val directory: String = if(startOfFile >= 0) path.splitAt(startOfFile)._1 + "/" else ""
          val tempFile: File = generateTempFile(directory)
          val fw = new FileWriter(tempFile, false)
          fw.write(rest.mkString("\n", "\n", ""))
          fw.write("\n" + sessionStart)
          fw.write("\n" + dtFormatter.format(LocalDateTime.now))
          fw.close()
          file.delete()
          tempFile.renameTo(file)
          file
        }
      }
      
      //restore Tree Object from File if no matching session found or restore from session file 
      val tree = if(session.isEmpty){
        println("restoring from file")
        val fw: Option[FileWriter] = Some(new FileWriter(sessionFile, true))
        val result = tactic match{
          case None => restoreProof(expr, defaultP, state, rws, "0", fw)
          case Some(tactic_) => restoreProof(expr, tactic_, state, rws, "0", fw)
        }
        fw match{
          case None => ()
          case Some(fw_) => fw_.close()
        }
        result
      }
      else {
        val fw = new FileWriter(sessionFile, true)
        for(line <- session){
          val split = line.split(seperator)
          val (index_, tactic_) = (split(0), split.drop(1).mkString)
          val goal_ = proofTree.getGoal(index_)
          goal_ match{
            case None => println("index " + index_ + ": not found")
            case Some(prop) => 
              var tactic__ : Tactic = Skip
              try{
                tactic__ = getTactic(tactic_, state, prop)
                step(prop, tactic__ , state, index_)
                fw.write("\n" + line)
              }
              catch{
                case e: Throwable => println("couldn't restore " + tactic_)
              }
          }
        }
        fw.close()
        proofTree
      }

      println("output to: " + sessionFile.toPath())
      StdIn.readLine("start session > ")
      (tree, sessionFile)
    }


    val (sessionTree, sessionFile) = restoreSession(expr, tactic, state, rws, sessionPath)
    proofTree = sessionTree
    val sessionWriter: FileWriter = new FileWriter(sessionFile, true)
    var opengoals = proofTree.getOpen
    var (currentIndex, currentGoal) : (String, Expr) = if(!opengoals.isEmpty) opengoals.head else ("0", proofTree.goal)
    

    while(!exit){
      println("\u001b[2J\u001B[0;0H") //clear visible screen + set cursor to (0,0)
      //goal + proof status
      if(proofTree.isClosed) {
        println(colorString("closed goal: " + expr.toString(), AnsiColor.GREEN))
        message += "\ngoal is closed - to leave this proof type 'exit'"
      }
      else println(colorString("open goal: " + expr.toString(), AnsiColor.RED))

      println("\n" + colorString(message, AnsiColor.YELLOW) + "\n")   //feedback
      println(TreePrinter.treeView(proofTree, currentIndex))          //proof Tree
      println(colorString("local context" , AnsiColor.BLUE) + "\n" +  //local context
              TreePrinter.formatProp(currentGoal))
      
      currentTactic = handleUserInput(state, currentGoal)

      if(storeTactic(currentTactic)){
        sessionWriter.write("\n" + currentIndex + seperator + TreePrinter.formatTactic(Some(currentTactic), false))
        sessionWriter.flush()
      }
      val (nextIndex, nextGoal, mssg) = step(currentGoal, currentTactic, state, currentIndex)
      currentIndex = nextIndex
      currentGoal = nextGoal
      message = mssg
    }

    sessionWriter.close()
    proofTree
  }

  def colorString(string: String, color: String): String = {
    s"${color}${string}${AnsiColor.RESET}"
  }

  /** 
   * @return true if new tactic can be applied at the current goal
   * false if current attempt has to be undone first
   */
  def viewMode(tree: Tree, goalName: String): Boolean = {
    tree.isClosed || (tree.getTactic(goalName) match{
      case None => false
      case Some(Skip) => false
      case _ => true
    })
  }

  /**
    * @return true if the tactic has to be stored in the session file
    * / is necessary to reconstruct the session
    *
    * @param tactic 
    * 
    */
  def storeTactic(tactic: Tactic): Boolean = tactic match{
    case Auto(_) | Induction(_, _) | Show(_) | Split | cuvee.iprove.Simplify | Sorry | Default(_)  => true
    case Undo(_) | Redo => true 
    case _ => false
  }

  /**
    * generates file at the given directory "foo/bar/"
    * file name: "temp" n ".txt" for the first n that doesn't yet exist
    * @param directory
    * @return the generated File Object
    */
  def generateTempFile(directory: String): File = {
    var fileName : String = "temp"
    val temp: String = "temp"
    var counter : Int = 2
    while(new File(directory + fileName + ".txt").exists){
      fileName = temp + counter
      counter += 1
    }
    new File(directory + fileName + ".txt")
  }

  def isTimestamp(input: String, datePattern: String): Boolean = {
    val format: SimpleDateFormat = new java.text.SimpleDateFormat(datePattern)
    try{
       format.parse(input)
       true
    }
    catch{
      case e: ParseException => false
    }
  }


  /**
    * @param currentIndex
    * @return index and goal of the next open subgoal
    */
  def nextOpenGoal(currentIndex: String, proofTree: Tree): (String, Expr) = {
    val opengoals = proofTree.getOpen
    if(opengoals.nonEmpty){
      val indexList = opengoals.map(goal => goal._1)
      val currentPos = indexList.indexOf(currentIndex)
      opengoals((currentPos + 1) % opengoals.length)
    }
    else{
      ("0", proofTree.goal)
    }
  }


  /** 
   * generates Tree structure from proof Tactics in the .bpl/.smt2 file 
   * @param fw FileWriter writes the applied tactics to output file
   * @return generated Tree
   * */ 
  def restoreProof(expr: Expr, tactic: prove.Proof, state: State, rws: Map[Fun, List[Rule]], index: String, fw: Option[FileWriter]): Tree = {
    fw match{
      case None => ()
      case Some(fw_) => fw_.write("\n" + index + " : " + TreePrinter.formatProveTactic(tactic.tactic))  
    }
    /*tactic match {
      case prove.Induction(variable, cases) => 
        //using variables names from iprove tactic to avoid inconsistent namings - leads to errors when restoring session
        val contGoals = Induction(variable).apply(expr, state, rws) 
        val contGoals2 = tactic.apply(state, expr) 
        assert(contGoals.length == contGoals2.length)
        val subgoals : List[Tree] = (contGoals zip contGoals2) map {
          case ((subgoal1, name),(subgoal2, Some(tactic))) => restoreProof(subgoal1, tactic, state, rws, index + name, fw)
          case ((subgoal1, name),(subgoal2, None)) => restoreProof(subgoal1, defaultP, state, rws, index + name, fw)
        }
        Step(expr, List(Attempt(Induction(variable), subgoals)), index, 0)

      case prove.Show(prop_, tactic_, cont) => 
        val subgoals = Show(prop_).apply(expr, state, rws)
        assert(subgoals.length == 2)
        val (first, second) = (subgoals(0), subgoals(1))
        val tactic__ = tactic_ match {
          case Some(tact) => tact
          case None => defaultP
        }
        val cont_ = cont match{
          case Some(tact) => tact
          case None => defaultP
        }
        val cases: List[Tree] = restoreProof(first._1, tactic__, state, rws,  (index + "0"), fw):: 
                                List(restoreProof(second._1, cont_, state, rws, (index + "1"), fw))
        Step(expr, List(Attempt(Show(prop_), cases)), index, 0)

      case prove.Auto => 
        val result = prover.apply(state, expr)
        val (goal_, _) = result.head
        if(goal_.equals(True)) Step(expr, List(Attempt(Auto(prover), Nil)), index, 0) 
        else             Step(expr, List(Attempt(Auto(prover), List(Step(result.head._1, Nil, (index + "fail"))))), index, 0) 
      
      //case prove.Debug(tactic_)  => restoreProof(expr, tactic_, state, rws, index, fw)
      case prove.NoAuto(tactic_) => restoreProof(expr, tactic_, state, rws, index, fw)
      case prove.Sorry           => Step(expr, List(Attempt(Sorry, Nil)), index, 0)
      //case prove.Skip | _        => Step(expr, Nil, index)
    }*/
    ???
  }



  def vars(goal: Expr): Map[String, Var] = goal match {
    case _ if(goal.isAtomic) =>
      Map()
    case Clause(xs, assms, concls) =>
      val names = xs map (_.name.toString)
      Map(names zip xs: _*)
  }

  def getScope(goal: Expr): Map[Name, Var] = goal match{
    case _ if(goal.isAtomic) => Map()
    case Clause(xs, assms, concls) => 
      val names = xs map(_.name)
      Map (names zip xs: _*)
  }

  /** handles exceptions when parsing user input to tactic  
   * @return the parsed iprove Tactic
  */
  def handleUserInput(state: State, currentGoal: Expr): Tactic = {
    try{
      getTactic(readLine("> "), state, currentGoal)
    }
    catch{
      case _: Throwable => 
        println("Something went wrong. Please try again")
        handleUserInput(state, currentGoal)
    }
  }

  
  //Regex pattern for calling open/down with specific number
  val selectPattern : Regex = "open (\\d+)".r
  val downPattern : Regex = "down (\\d+)".r

  /** maps String to iprove Tactic Object */
  def getTactic(input: String, state: State, goal: Expr): Tactic = input.trim match{
    //tactics (induction + show below)
    case "split" => Split
    case "sorry" => Sorry
    case "auto"  => Auto(prover)
    case "simplify" => cuvee.iprove.Simplify

    //attempt management
    case "undo" => Undo(false)
    case "undo here" => Undo(true)
    case "redo" => Redo
    
    //navigation
    case "up" => Up
    case "down" => SelectChild(-1)
    case "open" => SelectGoal(-1)
    case "skip" | "" => Skip

    //util
    case "check" => Check //not necessary anymore
    case "help" => Help
    case "exit" => Exit
    case "proof" => Proof
    case "rules" => RwRules
    case "goal" => cuvee.iprove.Goal

    case selectPattern(nr) => SelectGoal(nr.toInt)
    case downPattern(nr) => SelectChild(nr.toInt)

    //show expression
    case line if line startsWith "show " =>
      val text = line drop "show ".length

      implicit val ctx: Map[Name, Param] = Map()
      implicit val scope: Map[Name, Var] = getScope(goal)
      val parser = new Parser(state)
      val grammar = new Grammar(parser)
      val reader = new StringReader(text)
      val phi: Expr = grammar.formula.parseAll(cuvee.boogie.scan(reader))
      Show(phi)

    //induction variable
    case line if line startsWith "induction " =>
      val text = line drop "induction ".length 
      val map : Map[String, Var] = vars(goal)
      val variable = map.get(text)
      variable match{
        case None => 
          println("variable " + text + " is not available")
          throw new Exception
        case Some(variable_) => Induction(variable_)
      }
    
    //cases variable
    case line if line startsWith "cases " =>
      val text = line drop "cases ".length 
      val map : Map[String, Var] = vars(goal)
      val variable = map.get(text)
      variable match{
        case None => 
          println("variable " + text + " is not available")
          throw new Exception
        case Some(variable_) => Induction(variable_, hyp = false)
      }
    
    //default tactic
    case line if line startsWith "default " => 
      val text = line drop "default ".length
      val tactic: Tactic = getTactic(text, state, goal)
      tactic match{
        case Auto(_) | Sorry | cuvee.iprove.Simplify | Split => ()
        case _ => println("This tactic is not available")
                  throw new Exception
      }
      Default(tactic) //not possible with show / induction 

    case _ => 
      println("Couldn't recognize that input. Please enter a valid tactic") 
      getTactic(readLine("> "), state, goal)
  }

}
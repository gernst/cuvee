package cuvee

import cuvee.backend.Tactic
import cuvee.pure._
import cuvee.smtlib._
import cuvee.backend.Prove
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.backend.Solver
import cuvee.util.Main
import cuvee.util.Run
import cuvee.backend.ProveSimple
import cuvee.backend.NoAuto

object fastexp extends Run(Cuvee, "examples/fastexp.smt2", "-debug:solver")

object Cuvee extends Main {
  def main(args: Array[String]) {
    val c = new Cuvee
    c.configure(args.toList)
    c.run_(c.cmds, c.state.get, z3(c.state.get))
  }
}

class Cuvee {
  var state: Option[State] = None
  var cmds: List[Cmd] = Nil

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case "-debug:solver" :: rest =>
        cuvee.smtlib.solver.debug = true
        configure(rest)

      case "-debug:scanner" :: rest =>
        cuvee.sexpr.debug = true
        configure(rest)

      case path :: rest if state.isDefined =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        val (cmds_, state_) = cuvee.boogie.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        val (cmds_, state_) = cuvee.smtlib.parse(path)
        state = Some(state_)
        cmds = cmds_
        configure(rest)

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  def show(phi: Expr, state: State, solver: Solver): Expr = {
    val prop = Disj.from(phi)

    val prove = new Prove(solver)
    val result = prove.prove(prop)
    val psi = result.toExpr

    if (psi != True) {
      for (line <- psi.lines)
        println(line)
    }

    phi
  }

  def run(cmds: List[Cmd], state: State, solver: Solver) {
    cmds match {
      case Nil =>

      case DeclareProc(name, in, out) :: rest =>

      case DefineProc(name, in, out, body) :: rest =>
        val xs = in ++ out
        val st = Expr.id(xs)
        val post = True
        val phi = Forall(xs, Eval.wp(WP, body, st, post))
        val cmd = Lemma(phi, None)

        run(cmd :: rest, state, solver)

      case SetOption("print-success", _) :: rest =>
        run(rest, state, solver)

      case (ctrl: Ctrl) :: rest =>
        // solver.control(ctrl)
        run(rest, state, solver)

      case (decl: Decl) :: rest =>
        solver.declare(decl)
        run(rest, state, solver)

      case Assert(Not(phi)) :: rest =>
        println("lemma")
        for (line <- phi.lines)
          println(line)
        val phi_ = show(phi, state, solver)
        solver.assert(Not(phi))
        run(rest, state, solver)

      case Assert(phi) :: rest =>
        // println("axiom " + phi)
        solver.assert(phi)
        run(rest, state, solver)

      case (cmd @ Lemma(phi, None)) :: rest if false =>
        val phi_ = show(phi, state, solver)
        run(rest, state, solver)

      case (cmd @ Lemma(phi, None)) :: rest =>
        val prove = new ProveSimple(solver)
        val phi_ = prove.prove(phi)

        if (!solver.isTrue(phi_)) {
          for (line <- phi_.lines)
            println(line)
        }

        run(rest, state, solver)

      case Labels :: rest =>
        // val result = solver.labels()
        run(rest, state, solver)

      case CheckSat :: rest =>
        val result = solver.check()
        println(result)
        run(rest, state, solver)

    }
  }

  def run_(cmds: List[Cmd], state: State, solver: Solver) {
    assert(this.state.isDefined, "No file was parsed")

    val prover = new Prove(solver)

    for (cmd ← cmds) {
      cmd match {
        case DeclareProc(name, in, out) =>

        case DefineProc(name, in, out, body) =>
          val xs = in ++ out
          val st = Expr.id(xs)
          val post = True
          val phi = Forall(xs, Eval.wp(WP, body, st, post))

          val status = solver.check(!phi)
          println("procedure " + name + ": " + status)

        case decl: Decl => solver.declare(decl)

        case Assert(phi) => solver.assert(phi)

        case Lemma(expr, tactic) => {
          println()
          println("================  LEMMA  ================")
          println("show:  " + expr)

          val normalized = Disj.from(expr)

          rec(normalized, tactic, 1)(state, solver, prover) match {
            case Atom(True) =>
              println("\u001b[92m✔\u001b[0m Lemma proved successfully!")
            case Atom(False) =>
              println(
                "\u001b[91m✘\u001b[0m The lemma is false and cannot be proven!"
              )
            case remaining =>
              println(
                "\u001b[91m⚠\u001b[0m Some subgoals could not be proven! Remaining combined goal: " + remaining.toExpr
              )
          }

          // In any case, assert the lemma, so that its statement is available in later proofs
          solver.assert(expr)
        }
        case _ =>
      }
    }
  }

  def rec(prop: Prop, tactic: Option[Tactic], depth: Int = 0)(implicit
      state: State,
      slv: Solver,
      prover: Prove
  ): Prop = {
    def indent(depth: Int, indentStr: String = "  "): String = {
      if (depth <= 0) return "";
      indentStr + indent(depth - 1, indentStr)
    }

    println(indent(depth) + "---  PROOF OBLIGATION ---")
    println(indent(depth) + "prop:     " + prop.toExpr)

    // Call the prover, except if instructed by the NoAuto tactic *not* to do so.
    // Sets `tactic_` to an `Option[Tactic]` of the tactic that should be applied to the remaining goal (if any)
    val (tactic_, prop_) = tactic match {
      case Some(NoAuto(tactic_)) =>
        // Skip the prover call and execute the inner tactic directly
        (Some(tactic_), prop)

      case _ =>
        // Call prover
        val res = prover.prove(prop)
        println(indent(depth) + "new goal: " + res.toExpr)

        // Set tactic_ to whatever tactic was beforehand
        (tactic, res)
    }

    // Apply the tactic `tactic_`
    val prop__ = tactic_ match {
      case Some(tactic_) => 
        println(indent(depth) + "tactic:   " + tactic)
        // Apply the tactic and get the remaining subgoals that we need to prove
        val goals = tactic_.apply(state, prop)

        // TODO: What do we return, if not all of the subgoals can be proven?
        //       Do we return /\ {unprovable subgoals} ?
        (goals map ({ case (prop_, tactic_) =>
          rec(prop_, tactic_, depth + 1)
        }) filter (_ != Atom(True))) match {
          case Nil             => Atom(True)
          case remaining_goals => Conj.from(And(remaining_goals map (_.toExpr)))
        }
      case None => prop_
    }

    // Call the simplifier
    val simp = Simplifier.simplify(prop__)
    println(indent(depth) + "simp:     " + simp.toExpr)

    simp match {
      case Atom(True) =>
        println(
          indent(depth) + f"\u001b[92m✔\u001b[0m Goal found to be `true`"
        )

      case Atom(False) =>
        println(
          indent(depth) + f"\u001b[91m✘\u001b[0m Goal found to be `false`"
        )

      case goal =>
        println(
          indent(depth) + f"\u001b[91m✘\u001b[0m Could not show goal ${prop.toExpr} automatically"
        )
    }

    // Return whatever remained
    simp
  }
}

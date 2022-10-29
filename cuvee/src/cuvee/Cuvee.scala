package cuvee

import cuvee.backend._
import cuvee.pure._
import cuvee.smtlib._
import cuvee.imp.Eval
import cuvee.imp.WP
import cuvee.util.Main
import cuvee.util.Run
import cuvee.util.Proving
import cuvee.util.Printer

object fastexp extends Run(Cuvee, "examples/fastexp.smt2")
object list extends Run(Cuvee, "examples/case_studies/list.bpl")
object debug extends Run(Cuvee, "-rewrite", "debug.bpl")

object Cuvee extends Main {
  def main(args: Array[String]) {
    val c = new Cuvee
    c.configure(args.toList)
    c.run(c.cmds, c.state, z3(c.state))
  }
}

class Cuvee {
  var state = State.default
  var cmds: List[Cmd] = Nil
  var printer: Printer = cuvee.smtlib.printer
  var rewrite: Boolean = false

  val options = Map(
    "-help" ->
      ("show help text", () => { help() }),
    "-debug:solver" ->
      ("show information on the interaction with the backend", () => {
        cuvee.smtlib.solver.debug = true
      }),
    "-debug:scanner" -> ("show list of parsed tokens (SMT-LIB only)", () => {
      cuvee.sexpr.debug = true
    }),
    "-debug:prover" -> ("show details about proof steps and tactic applications", () =>
      {
        cuvee.util.Proving.debug = true
      }),
    "-print:smtlib" -> ("override printer to output SMT-LIB format", () => {
      this.printer = cuvee.smtlib.printer
    }),
    "-print:boogie" -> ("override printer to output Boogie format", () => {
      this.printer = cuvee.boogie.printer
    }),
    "-rewrite" -> ("apply structurally recursive axioms as rewrite rules", () =>
      {
        this.rewrite = true
      })
  )

  def help() {
    println("cuvee [options] <file>")
    for ((flag, (description, _)) <- options) {
      println("  " + flag)
      println("      " + description)
      println()
    }
  }

  def configure(args: List[String]) {
    args match {
      case Nil =>

      case first :: rest if options contains first =>
        val (_, action) = options(first)
        action()
        configure(rest)

      case "-rewrite" :: rest =>
        rewrite = true
        configure(rest)

      case path :: rest if cmds.nonEmpty =>
        cuvee.error(
          "A file was already loaded. At the moment only a single input file is supported."
        )

      case path :: rest if path.endsWith(".bpl") =>
        val (cmds_, state_) = cuvee.boogie.parse(path)
        printer = cuvee.boogie.printer
        state = state_
        cmds = cmds_
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        val (cmds_, state_) = cuvee.smtlib.parse(path)
        printer = cuvee.smtlib.printer
        state = state_
        cmds = cmds_
        configure(rest)

      case path :: rest =>
        error(
          f"Could not parse file at path ${path}: Format could not be determined as the path does't end in .bpl or .smt2."
        )
    }
  }

  // TODO: Figure out, whether or how to integrate these commands
  // def old_run(cmds: List[Cmd], state: State, solver: Solver) {
  //   cmds match {
  //     case Assert(Not(phi)) :: rest =>
  //       println("lemma")
  //       for (line <- phi.lines)
  //         println(line)
  //       val phi_ = show(phi, state, solver)
  //       solver.assert(Not(phi))
  //       run(rest, state, solver)

  //     case (cmd @ Lemma(phi, None)) :: rest if false =>
  //       val phi_ = show(phi, state, solver)
  //       run(rest, state, solver)

  //     case (cmd @ Lemma(phi, None)) :: rest =>
  //       val prove = new ProveSimple(solver)
  //       val phi_ = prove.prove(phi)

  //       if (!solver.isTrue(phi_)) {
  //         for (line <- phi_.lines)
  //           println(line)
  //       }

  //       run(rest, state, solver)

  //   }
  // }

  def run(cmds: List[Cmd], state: State, solver: Solver) {
    // assert(cmds.nonEmpty, "No file was parsed")

    solver.exec(SetOption("produce-models", true))
    solver.exec(SetOption("produce-assignments", true))

    val prover = new Prove(solver)
    val rules = Rewrite.from(cmds, state)
    val safe = Rewrite.safe(rules, state) groupBy (_.fun)

    for (cmd ← cmds) {
      cmd match {
        case DeclareProc(name, in, out) =>

        case DefineProc(name, in, out, body) =>
          val xs = in ++ out
          val st = Expr.id(xs)
          val post = True
          val phi = Forall(xs, Eval.wp(WP, body, st, post))

          // println("procedure " + name)
          Proving.show(Disj.from(phi), None)(
            state,
            solver,
            prover,
            printer,
            safe
          )

        // rec(Disj.from(phi), None, 1)(state, solver, prover)

        // solver.scoped {
        //   solver.assert(!phi)
        //   val status = solver.check()

        //   if (status == Sat) {
        //     solver.model()
        //   }

        // }

        case ctrl: Ctrl =>
        // solver.control(ctrl)

        case decl: Decl =>
          solver.declare(decl)

        case Assert(phi) =>
          // println("axiom " + phi)
          solver.assert(phi)

        case Lemma(expr, tactic) =>
          // println()
          // println("================  LEMMA  ================")
          // println("show:  " + expr)

          Proving.show(Disj.from(expr), tactic)(
            state,
            solver,
            prover,
            printer,
            safe
          )

          // In any case, assert the lemma, so that its statement is available in later proofs
          solver.assert(expr)

        case Labels =>
        // val result = solver.labels()

        case CheckSat =>
          val result = solver.check()
          println(result)
      }
    }
  }
}

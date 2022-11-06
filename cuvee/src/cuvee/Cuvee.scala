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
import cuvee.imp.Spec

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
  var rewrite: Boolean = false

  implicit var printer: Printer = cuvee.smtlib.printer

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
    "-debug:prover" -> ("show details about proof steps and tactic applications", () => {
      cuvee.util.Proving.debug = true
    }),
    "-print:smtlib" -> ("override printer to output SMT-LIB format", () => {
      this.printer = cuvee.smtlib.printer
    }),
    "-print:boogie" -> ("override printer to output Boogie format", () => {
      this.printer = cuvee.boogie.printer
    }),
    "-rewrite" -> ("apply structurally recursive axioms as rewrite rules", () => {
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
        try {
          val (cmds_, state_) = cuvee.boogie.parse(path)
          printer = cuvee.boogie.printer
          state = state_
          cmds = cmds_
        } catch {
          case error: arse.Error =>
            println(error)
        }
        configure(rest)

      case path :: rest if path.endsWith(".smt2") =>
        try {
          val (cmds_, state_) = cuvee.smtlib.parse(path)
          printer = cuvee.smtlib.printer
          state = state_
          cmds = cmds_
        } catch {
          case error: arse.Error =>
            println(error)
        }
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

    def prove(phi: Expr, tactic: Option[Tactic]) {
      Proving.show(Disj.from(phi), tactic)(
        state,
        solver,
        prover,
        printer,
        safe
      )
      // val phi_ = Simplify.simplify(phi, safe)
      // if (!solver.isTrue(phi)) {
      //   val cmd = Lemma(phi_, None)
      //   for (line <- cmd.lines)
      //     println(line)
      // }
    }

    def exec(cmd: Cmd) = cmd match {
      case DeclareProc(name, in, out) =>

      case DefineProc(name, in, out, spec, body) =>
        val (ys, pre, post) = spec match {
          case None                      => (Nil, True, True)
          case Some(Spec(xs, pre, post)) => (xs, pre, post)
        }

        val su = Expr.subst(in, Old(in))

        val xs = in ++ out ++ ys
        val post_ = post subst su
        val st = Expr.id(xs)

        val phi = Forall(xs, pre ==> Eval.wp_proc(WP, body, st, post_))

        prove(phi, tactic = None)

      case ctrl: Ctrl =>
      // solver.control(ctrl)

      case decl: Decl =>
        solver.declare(decl)

      case Assert(phi) =>
        // println("axiom " + phi)
        solver.assert(phi)

      case Lemma(phi, tactic) =>
        // println()
        // println("================  LEMMA  ================")
        // println("show:  " + expr)
        prove(phi, tactic)

        // In any case, assert the lemma, so that its statement is available in later proofs
        solver.assert(phi)

      case Labels =>
      // val result = solver.labels()

      case CheckSat =>
        val result = solver.check()
        println(result)
    }

    for (cmd ← cmds) {
      try {
        exec(cmd)
      } catch {
        case bad: smtlib.Error =>
          for (line <- bad.lines)
            println(line)
      }
    }
  }
}

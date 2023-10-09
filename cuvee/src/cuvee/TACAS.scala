package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr

object TACAS {
  def main(args: Array[String]) {
    // something like evaluation/lemmas/tree
    val Array(basepath) = args

    val (cmds, st) = parse(basepath + ".bpl")

    implicit val solver = Solver.z3(100)
    // Solver.debug = true

    for (cmd <- cmds)
      solver.ack(cmd)

    def lemmasOf(file: String) = if (file endsWith ".th.log") {
      cuvee.thesy.storedLemmas(file, st)
    } else {
      val (cmds, _) = parse(file)
      cmds collect { case Lemma(phi, _, _) => phi }
    }

    case class Stats(lemmas: List[Expr]) {
      def nontrivial = lemmas.nontrivial
      def reduced = lemmas.reduced
    }

    val structural = Stats { lemmasOf(basepath + ".structural.bpl") }
    val conditional = Stats { lemmasOf(basepath + ".conditional.bpl") }
    val enumerate = Stats { lemmasOf(basepath + ".enumerate.bpl") }
    val thesy = Stats { lemmasOf(basepath + ".th.log") }

    import util.TheoryComparison

    def printDefinition(g: String, s: String, l: List[Expr]) = {
      println("\\newcommand{\\" + g + s + "}{" + l.length + "}")
    }

    def makeGraph(g: String, a: Stats, b: Stats, c: Stats, d: Stats) {
      printDefinition(g, "A", a.reduced)
      printDefinition(g, "B", a.nontrivial)
      printDefinition(g, "C", a.lemmas)
      println()

      printDefinition(g, "D", a.reduced validatedBy b.reduced)
      printDefinition(g, "E", a.nontrivial validatedBy b.nontrivial)
      printDefinition(g, "F", a.lemmas validatedBy b.lemmas)
      println()

      printDefinition(g, "G", a.reduced validatedBy c.reduced)
      printDefinition(g, "H", a.nontrivial validatedBy c.nontrivial)
      printDefinition(g, "I", a.lemmas validatedBy c.lemmas)
      println()

      printDefinition(g, "J", a.reduced validatedBy d.reduced)
      printDefinition(g, "K", a.nontrivial validatedBy d.nontrivial)
      printDefinition(g, "L", a.lemmas validatedBy d.lemmas)
      println()
    }

    println("% " + basepath + ".bpl")
    println()

    println("% group: structural")
    makeGraph("x", structural, conditional, enumerate, thesy)
    println()

    println("% group: conditional")
    makeGraph("y", conditional, structural, enumerate, thesy)
    println()

    println("% group: enumerate")
    makeGraph("z", enumerate, structural, conditional, thesy)
    println()

    println("% group: thesy")
    makeGraph("w", thesy, structural, conditional, enumerate)
    println()
  }
}
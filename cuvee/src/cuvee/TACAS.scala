package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr

object TACAS {
  def main(args: Array[String]) {
    // something like evaluation/lemmas/tree
    val Array(mode, basepath) = args

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

    case class Stats(name: String, lemmas: List[Expr]) {
      def nontrivial = lemmas.nontrivial
      def reduced = lemmas.reduced
    }

    val structural = Stats("structural", lemmasOf(basepath + ".structural.bpl"))
    val conditional = Stats("conditional", lemmasOf(basepath + ".conditional.bpl"))
    val enumerate = Stats("enumerate", lemmasOf(basepath + ".enumerate.bpl"))
    val thesy = Stats("thesy", lemmasOf(basepath + ".th.log"))

    import util.TheoryComparison

    def printDefinition(g: String, s: String, l: List[Expr]) = {
      println("\\newcommand{\\" + g + s + "}{" + l.length + "}")
    }

    def makeGraph(g: String, a: Stats, b: Stats, c: Stats, d: Stats) {
      println("% group: " + a.name)

      val reduced = a.reduced
      val nontrivial = a.nontrivial
      val lemmas = a.lemmas

      printDefinition(g, "A", reduced)
      printDefinition(g, "B", nontrivial)
      printDefinition(g, "C", lemmas)
      println()

      printDefinition(g, "D", reduced validatedBy b.reduced)
      printDefinition(g, "E", nontrivial validatedBy b.nontrivial)
      printDefinition(g, "F", lemmas validatedBy b.lemmas)
      println()

      printDefinition(g, "G", reduced validatedBy c.reduced)
      printDefinition(g, "H", nontrivial validatedBy c.nontrivial)
      printDefinition(g, "I", lemmas validatedBy c.lemmas)
      println()

      printDefinition(g, "J", reduced validatedBy d.reduced)
      printDefinition(g, "K", nontrivial validatedBy d.nontrivial)
      printDefinition(g, "L", lemmas validatedBy d.lemmas)
      println()

      println()
    }

    def printList(h: String, es: List[Expr]) {
      println(h)
      println()
      for (e <- es)
        println("    " + e)
      println()
    }

    def makeList(n: String, a: Stats, b: Stats, c: Stats, d: Stats) {

      val a_reduced = a.reduced
      val a_implied = a.nontrivial filterNot a_reduced.contains
      val a_good = a_reduced ++ a_implied
      val a_lemmas = a.lemmas filterNot a_good.contains

      val b_reduced = a_reduced validatedBy b.reduced
      val c_reduced = a_reduced validatedBy c.reduced
      val d_reduced = a_reduced validatedBy d.reduced

      val b_implied = a_implied validatedBy b.nontrivial
      val c_implied = a_implied validatedBy c.nontrivial
      val d_implied = a_implied validatedBy d.nontrivial

      val b_lemmas = a_lemmas validatedBy b.lemmas
      val c_lemmas = a_lemmas validatedBy c.lemmas
      val d_lemmas = a_lemmas validatedBy d.lemmas

      val a_confirmed = b_lemmas ++ c_lemmas ++ d_lemmas
      val a_unique = a_lemmas filterNot a_confirmed.contains
      val b_unique = a_lemmas filterNot b_lemmas.contains
      val c_unique = a_lemmas filterNot c_lemmas.contains
      val d_unique = a_lemmas filterNot d_lemmas.contains

      println("# benchmark: " + n + " comparison for " + a.name)
      println()

      println("## lemmas found by " + a.name)
      println()
      printList("### reduced", a_reduced)
      printList("### implied", a_implied)
      printList("### trivial", a_lemmas)
      println()

      println("## unique lemmas found by " + a.name)
      println()
      printList("### overall unique", a_unique)
      printList("### unique over " + b.name, b_unique)
      printList("### unique over " + c.name, c_unique)
      printList("### unique over " + d.name, d_unique)
      println()

      // println("## lemmas confirmed by " + b.name)
      // println()
      // printList("### reduced", b_reduced)
      // printList("### implied", b_implied)
      // printList("### trivial", b_lemmas)
      // println()

      // println("## lemmas confirmed by " + c.name)
      // println()
      // printList("### reduced", c_reduced)
      // printList("### implied", c_implied)
      // printList("### trivial", c_lemmas)
      // println()

      // println("## lemmas confirmed by " + d.name)
      // println()
      // printList("### reduced", d_reduced)
      // printList("### implied", d_implied)
      // printList("### trivial", d_lemmas)
      // println()

      println()
    }

    if (mode == "tex") {
      println("% " + basepath + ".bpl")
      println()

      makeGraph("x", structural, conditional, enumerate, thesy)
      makeGraph("y", conditional, structural, enumerate, thesy)
      makeGraph("z", enumerate, structural, conditional, thesy)
      makeGraph("w", thesy, structural, conditional, enumerate)
    } else if (mode == "md") {
      makeList(basepath, structural, conditional, enumerate, thesy)
      makeList(basepath, conditional, structural, enumerate, thesy)
      makeList(basepath, enumerate, structural, conditional, thesy)
      makeList(basepath, thesy, structural, conditional, enumerate)
    }
  }
}

package cuvee

import cuvee.smtlib.Solver
import cuvee.smtlib.Lemma
import cuvee.pure.Expr
import java.io.PrintStream
import java.io.FileOutputStream

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

    case class Stats(name: String, lemmas: List[Expr]) {
      val nontrivial = lemmas.nontrivial
      val reduced = nontrivial.reducedGreedily
      val implied = nontrivial -- reduced
      val trivial = lemmas -- nontrivial

      assert(
        reduced subsetOf nontrivial,
        "reduced lemmas not in nontrivial: " + (reduced -- nontrivial)
      )

      assert(
        nontrivial subsetOf lemmas,
        "nontrivial lemmas not in lemmas: " + (nontrivial -- lemmas)
      )
    }

    val structural = Stats("structural", lemmasOf(basepath + ".structural.bpl"))
    val conditional = Stats("conditional", lemmasOf(basepath + ".conditional.bpl"))
    val enumerate = Stats("enumerate", lemmasOf(basepath + ".enumerate.bpl"))
    val thesy = Stats("thesy", lemmasOf(basepath + ".th.log"))

    val tex = new PrintStream(new FileOutputStream(basepath + ".tex"))
    val md = new PrintStream(new FileOutputStream(basepath + ".md"))

    import util.TheoryComparison

    def printDefinition(g: String, s: String, l: List[Expr]) = {
      tex.println("\\newcommand{\\" + g + s + "}{" + l.length + "}")
    }

    def makeGraph(g: String, a: Stats, b: Stats, c: Stats, d: Stats) {

      val reduced = a.reduced
      val nontrivial = a.nontrivial
      val lemmas = a.lemmas
    }

    def printList(h: String, es: List[Expr]) {
      md.println(h)
      md.println()
      for (e <- es)
        md.println("    " + e)
      md.println()
    }

    def makeList(n: String, g: String, a: Stats, b: Stats, c: Stats, d: Stats) {
      val b_reduced = a.reduced validatedBy b.reduced
      val c_reduced = a.reduced validatedBy c.reduced
      val d_reduced = a.reduced validatedBy d.reduced

      val b_nontrivial = a.nontrivial validatedBy b.nontrivial
      val c_nontrivial = a.nontrivial validatedBy c.nontrivial
      val d_nontrivial = a.nontrivial validatedBy d.nontrivial

      val b_lemmas = a.lemmas validatedBy b.lemmas
      val c_lemmas = a.lemmas validatedBy c.lemmas
      val d_lemmas = a.lemmas validatedBy d.lemmas

      val a_confirmed = b_lemmas ++ c_lemmas ++ d_lemmas
      val a_unique = a.lemmas -- a_confirmed
      val b_unique = a.lemmas -- b_lemmas
      val c_unique = a.lemmas -- c_lemmas
      val d_unique = a.lemmas -- d_lemmas

      tex.println("% group: " + a.name)

      printDefinition(g, "A", a.reduced)
      printDefinition(g, "B", a.nontrivial)
      printDefinition(g, "C", a.lemmas)
      tex.println()

      printDefinition(g, "D", b_reduced)
      printDefinition(g, "E", b_nontrivial)
      printDefinition(g, "F", b_lemmas)
      tex.println()

      printDefinition(g, "G", c_reduced)
      printDefinition(g, "H", c_nontrivial)
      printDefinition(g, "I", c_lemmas)
      tex.println()

      printDefinition(g, "J", d_reduced)
      printDefinition(g, "K", d_nontrivial)
      printDefinition(g, "L", d_lemmas)
      tex.println()
      tex.println()

      md.println("# benchmark: " + n + " comparison for " + a.name)
      md.println()

      md.println("## lemmas found by " + a.name)
      md.println()
      printList("### reduced", a.reduced)
      printList("### implied", a.nontrivial -- a.reduced)
      printList("### trivial", a.lemmas -- a.reduced -- a.nontrivial)
      md.println()

      md.println("## unique lemmas found by " + a.name)
      md.println()
      printList("### overall unique", a_unique)
      printList("### unique over " + b.name, b_unique)
      printList("### unique over " + c.name, c_unique)
      printList("### unique over " + d.name, d_unique)
      md.println()

      md.println("## lemmas confirmed by " + b.name)
      md.println()
      printList("### reduced", b_reduced)
      printList("### implied", b_nontrivial -- b_reduced)
      printList("### trivial", b_lemmas -- b_reduced -- b_nontrivial)
      md.println()

      md.println("## lemmas confirmed by " + c.name)
      md.println()
      printList("### reduced", c_reduced)
      printList("### implied", c_nontrivial -- c_reduced)
      printList("### trivial", c_lemmas -- c_reduced -- c_nontrivial)
      md.println()

      md.println("## lemmas confirmed by " + d.name)
      md.println()
      printList("### reduced", d_reduced)
      printList("### implied", d_nontrivial -- d_reduced)
      printList("### trivial", d_lemmas -- d_reduced -- d_nontrivial)
      md.println()

      md.println()
    }

    tex.println("% " + basepath + ".bpl")
    tex.println()

    makeList(basepath, "x", structural, conditional, enumerate, thesy)
    makeList(basepath, "y", conditional, structural, enumerate, thesy)
    makeList(basepath, "z", enumerate, structural, conditional, thesy)
    makeList(basepath, "w", thesy, structural, conditional, enumerate)
  }
}

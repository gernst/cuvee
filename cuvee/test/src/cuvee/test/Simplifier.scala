package cuvee.test

import cuvee.Cuvee
import minitest._

import java.io.File

import cuvee.smtlib.Lemma
import cuvee.smtlib.Goal
import cuvee.pure.False
import cuvee.pure.True
import cuvee.smtlib.Cmd

object Simplifier extends SimpleTestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/simplify/")

  val flags = Array("-simplify2")

  test("lt") {
    val lt = new File(testResources, "arithmetic/lt.bpl")
    val lemmas = Cuvee.collect(lt.toString +: flags)
    val LT_COUNT = 6 - 2 // |all goals| - |goals{:ex_true}|
    assert(lemmas.length == LT_COUNT)
    val result = test_comparison(lemmas)
    if (result.nonEmpty) {
      for (l <- result) l match {
        case Lemma(expr, _, _, _) =>
          val expected = "forall i: Int :: ((4 * i) < 1)"
          assert(expr.toString == expected)
      }
    } else
      assert(
        false,
        s"There should be at least one {:ex_simp} test goal in lt.bpl. Got 0."
      )
  }

  test("le") {
    val le = new File(testResources, "arithmetic/le.bpl")
    val lemmas = Cuvee.collect(le.toString +: flags)
    val LE_COUNT = 6 - 4
    assert(lemmas.length == LE_COUNT)
    val result = test_comparison(lemmas)
    if (result.nonEmpty)
      assert(
        false,
        s"Currently there are no {:ex_simp} test goals in le.bpl. Expected empty, got $result."
      )
  }

  /* Handle all cases that can be completely simplified at once.
   * Return the complicated ones for specific handling. */
  def test_comparison(lemmas: List[Cmd]): List[Cmd] = {
    var ret: List[Cmd] = List()
    for (l <- lemmas) yield l match {
      case Lemma(expr, _, Some(Goal), attrs) if attrs contains "ex_false" =>
        assert(expr == False, s"Annotation = $attrs, Expr = $expr.")
      case Lemma(expr, _, Some(Goal), attrs) if attrs contains "ex_true" =>
        assert(
          false,
          s"Cuvee does not leave `goal true` in its Lemmas. Got annotation = $attrs, expr = $expr"
        )
      case Lemma(expr, _, Some(Goal), attrs) if attrs contains "ex_simp" =>
        ret = ret :+ l
      case Lemma(expr, _, Some(Goal), attrs) =>
        assert(
          false,
          s"All test goals need to have an annotation. Got annotation = $attrs, expr = $expr"
        )
    }
    ret
  }
}

package cuvee.test

import cuvee.Cuvee
import minitest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileOutputStream
import cuvee.pure.Simplify
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Success
import cuvee.smtlib.Unknown
import cuvee.smtlib.Unsupported
import cuvee.smtlib.Lemma
import cuvee.smtlib.Goal

object Verify extends SimpleTestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")

  
  val annotated = new File(testResources, "annotated")
  val annotatedFiles = find(annotated, ".bpl", exclude = List("simplify", "induction"))

  for (file <- annotatedFiles) {
    val task = file.toString
    val args = Array("-vcgen:partial", "-split", "-z3", task)
    test(task){
      Cuvee.main(args)
    }
  }

  val inductionFiles = find(new File(testResources, "induction"), ".bpl", Nil)
  
  for (file <- inductionFiles){
    val task = file.toString
    val args = Array("-prove:z3", "-z3", task)
    val cmds = Cuvee.collect(args)
    test(task){
      assert(cmds.forall{
        case Lemma(expr, proof, None, _) => false
        case Lemma(expr, proof, Some(Goal), _) => false
        case _ => true
      })
      Cuvee.main(args)
    }
  }
}

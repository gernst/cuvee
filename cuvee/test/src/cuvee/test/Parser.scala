package cuvee.test

import cuvee.Cuvee
import minitest._

import java.io.ByteArrayOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.BufferedReader
import java.io.InputStreamReader
import cuvee.boogie.parse
import cuvee.smtlib.Cmd

object Parser extends SimpleTestSuite {
  val testResources = new File("cuvee/test/src/cuvee/resources/")
  
  val stream = new ByteArrayOutputStream
  System.setOut(new java.io.PrintStream(stream))

  val boogiefiles = find(testResources, ".bpl", exclude = List("simplify", "smtlib"))
  for (file <- boogiefiles) {
    val task = file.toString
    val fst = Cuvee.collect(Array(task))
    
    val parser = (reader: BufferedReader) => cuvee.boogie.parse(reader)
    val snd = parseFile(file.getAbsolutePath(), parser)

    test("boogie: " + task){
      assert(fst == snd)
    }
  }
  
  val smtlib = new File(testResources, "smtlib")
  val smtfiles = find(smtlib, ".smt2", exclude = Nil)
  
  for (file <- smtfiles) {
    val task = file.toString
    val fst = Cuvee.collect(Array(task))
    
    val parser = (reader: BufferedReader) => cuvee.smtlib.parse(reader)
    val snd = parseFile(file.getAbsolutePath(), parser)

    test("smtlib: " + task){
      assert(fst == snd)
    }
  }


  def parseFile(path: String, parser : BufferedReader => (List[Cmd], _)): List[Cmd] = {
    val fileStream = new FileInputStream(path)
    val reader = new BufferedReader(new InputStreamReader(fileStream))
    val (snd, _) = parser(reader)
    fileStream.close()
    reader.close()
    snd
  }
}



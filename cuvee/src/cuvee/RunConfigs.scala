package cuvee
import cuvee.util.Run
import cuvee.Cuvee

object testInduction extends Run(Cuvee, "examples/boogie/mergesort.bpl", "-prove:z3")

object listAppend extends Run(Cuvee, "examples/boogie/simple.bpl", "-prove:z3")


object testShow extends Run(Cuvee, "examples/boogie/list.bpl", "-prove:z3")


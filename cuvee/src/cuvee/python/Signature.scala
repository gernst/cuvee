package cuvee.python

import cuvee.State
import cuvee.pure.Sugar
import cuvee.pure.Assoc
import cuvee.pure.Var

class Signature(state: State) {
  val pyValue = state.sort("pyValue")
  val pyNone = state.funs("pyNone", 0)

  val pyResult = Var("pyResult", pyValue)

  val int = state.sort("Int")
  val pyInt = state.funs("pyInt", 1)
  val pyGetInt = state.funs("pyGetInt", 1)

  val bool = state.sort("Bool")
  val pyBool = state.funs("pyBool", 1)
  val pyGetBool = state.funs("pyGetBool", 1)

  val pyArray = state.funs("pyArray", 2)
  val pyGetLength = state.funs("pyGetLength", 1)
  val pyGetArray = state.funs("pyGetValues", 1)

  val pyTrue = state.funs("pyTrue", 0)
  val pyFalse = state.funs("pyFalse", 0)
  val pyDefaultArray = state.funs("pyDefaultArray", 0)

  val pyIsTrue = state.funs("pyIsTrue", 1)

  val pyIte = state.funs("pyIte", 3)
  object pyAnd
      extends Sugar.commutative(state.funs("pyAnd", 2), pyTrue(), Assoc.right)
  object pyOr
      extends Sugar.commutative(state.funs("pyOr", 2), pyFalse(), Assoc.right)
  val pyNot = state.funs("pyNot", 1)
  val pyImplies = state.funs("pyImplies", 2)

  val pyEquals = state.funs("pyEquals", 2)
  val pyLessThan = state.funs("pyLessThan", 2)
  val pyLessEquals = state.funs("pyLessEquals", 2)
  val pyGreaterThan = state.funs("pyGreaterThan", 2)
  val pyGreaterEquals = state.funs("pyGreaterEquals", 2)

  val pyIn = state.funs("pyIn", 2)
  val pySelect = state.funs("pySelect", 2)
  val pyStore = state.funs("pyStore", 3)
  val pyShift = state.funs("pyShift", 2)
  val pyConcat = state.funs("pyConcat", 3)
  val pySlice = state.funs("pySlice", 3)

  val pyAdd = state.funs("pyAdd", 2)
  val pyNegate = state.funs("pyNegate", 1)
  val pySub = state.funs("pySub", 2)
  val pyTimes = state.funs("pyTimes", 2)
  val pyFloorDiv = state.funs("pyFloorDiv", 2)
  val pyMod = state.funs("pyMod", 2)
  // TODO only support if boogie has this operator
  // val pyPow = state.funs("pyPow", 2)
}

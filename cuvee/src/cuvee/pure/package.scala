package cuvee

package object pure {
  implicit def toVarList(vars: List[Var]) = new VarList(vars)
  implicit def toExprList(exprs: List[Expr]) = new ExprList(exprs)
  implicit def toParamList(params: List[Param]) = new ParamList(params)
  implicit def toTypeList(types: List[Type]) = new TypeList(types)
  // implicit def toCaseList(cases: List[Case]) = new CaseList(cases)

  val True = App(Fun.true_, Nil)
  val False = App(Fun.false_, Nil)

  val Zero = Lit(0, Sort.int)
  val One = Lit(1, Sort.int)
}

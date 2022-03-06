package cuvee

package object pure {
  implicit def toVarList(vars: List[Var]) = new VarList(vars)
  implicit def toExprList(exprs: List[Expr]) = new ExprList(exprs)
  implicit def toParamList(params: List[Param]) = new ParamList(params)
  implicit def toTypeList(types: List[Type]) = new TypeList(types)
  implicit def toCaseList(cases: List[Case]) = new CaseList(cases)

  // work around initialization order, not using Const
  object True extends App(Inst(Fun.true_, Map()), Nil)
  object False extends App(Inst(Fun.false_, Map()), Nil)

  def bool(b: Boolean) =
    if(b) True else False

  val Zero = Lit(0, Sort.int)
  val One = Lit(1, Sort.int)
}

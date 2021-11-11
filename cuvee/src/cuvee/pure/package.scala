package cuvee

package object pure {
  def require(phi: => Boolean, msg: => String) {
      assert(phi, msg)
  }

  implicit def toVarList(vars: List[Var]) = new VarList(vars)
  implicit def toExprList(exprs: List[Expr]) = new ExprList(exprs)
  implicit def toParamList(params: List[Param]) = new ParamList(params)
  implicit def toTypeList(types: List[Type]) = new TypeList(types)
}

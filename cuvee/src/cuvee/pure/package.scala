package cuvee

package object pure {
  def require(phi: => Boolean, msg: => String) {
      assert(phi, msg)
  }

  object Fail extends Throwable {
    override def fillInStackTrace(): Throwable = this
  }

  def fail = throw Fail

  implicit class Control[A](a: => A) {
    def or[B >: A](b: => B): B = {
      try { a }
      catch { case Fail => b}
    }
  }

  implicit def toVarList(vars: List[Var]) = new VarList(vars)
  implicit def toExprList(exprs: List[Expr]) = new ExprList(exprs)
  implicit def toParamList(params: List[Param]) = new ParamList(params)
  implicit def toTypeList(types: List[Type]) = new TypeList(types)
}

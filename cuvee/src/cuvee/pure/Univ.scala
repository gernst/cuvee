package cuvee.pure

object Univ {
  def apply(cons: (String, Con)*): Univ = {
    Univ(cons.toMap)
  }

  def param(name: String): Param = {
    Param(name)
  }

  def con(name: String, arity: Int = 0): Con = {
    Con(name, arity)
  }
}

case class Univ(cons: Map[String, Con]) {
  def sort(name: String, args: List[Type] = Nil): Sort = {
    val con = cons(name)
    if (con.arity != args.length) fail
    Sort(con, args)
  }
}
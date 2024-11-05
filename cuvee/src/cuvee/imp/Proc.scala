package cuvee.imp

import cuvee.util.Name
import cuvee.pure._
import cuvee.State

case class Proc(
    name: Name,
    params: List[Param],
    in: List[Var],
    out: List[Var],
    spec: Option[Spec]
) {}

sealed trait Mode
object Mode {
  case object In extends Mode { override def toString = "in" }
  case object Out extends Mode { override def toString = "out" }
  case object InOut extends Mode { override def toString = "inout" }
}

case class Contracts(
    name: Name,
    params: List[Param],
    formals: List[(Mode, Var)],
    contracts: List[(Expr, Expr)]
)

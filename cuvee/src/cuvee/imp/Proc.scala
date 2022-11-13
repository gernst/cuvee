package cuvee.imp

import cuvee.util.Name
import cuvee.pure._

case class Proc(
    name: Name,
    params: List[Param],
    in: List[Var],
    out: List[Var],
    spec: Option[Spec]
) {}

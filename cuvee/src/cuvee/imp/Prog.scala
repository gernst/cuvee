package cuvee.imp

import cuvee.pure._

object Skip extends Block(Nil)
object Old extends Sugar.unary(old)

sealed trait Modality /* extends ((Prog, Expr) => Expr) */ {
  def spec(xs: List[Var], pre: Expr, post: Expr): Expr
  def split(cond: Expr, left: Expr, right: Expr): Expr

  // def apply(prog: Prog, post: Expr) = {
  //   Post(this, prog, post)
  // }

  // def apply(body: Body, post: Expr) = {
  //   quant(body.locals, Post(this, body.prog, post))
  // }

  // def unapply(expr: Post) =
  //   expr match {
  //     case Post(how, prog, post) if how == this =>
  //       Some((prog, post))
  //     case _ =>
  //       None
  //   }
}

case object Box extends Modality {
  def spec(xs: List[Var], pre: Expr, post: Expr) =
    Forall(xs, pre ==> post)

  def split(cond: Expr, left: Expr, right: Expr) =
    (cond ==> left) && (!cond ==> right)
}

case object WP extends Modality {
  def spec(xs: List[Var], pre: Expr, post: Expr) =
    Forall(xs, pre ==> post)

  def split(cond: Expr, left: Expr, right: Expr) =
    (cond ==> left) && (!cond ==> right)
}

case object Dia extends Modality {
  def spec(xs: List[Var], pre: Expr, post: Expr) =
    Exists(xs, pre && post)

  def split(cond: Expr, left: Expr, right: Expr) =
    (cond && left) || (!cond && right)
}

/*
case class Post(how: Modality, prog: Prog, post: Expr) extends Expr {
  def free = prog.read ++ post.free // XXX: overapproximation
  def rename(re: Map[Var, Var]) = Post(how, prog replace re, post rename re)
  def subst(su: Map[Id, Expr]) = ???
  override def toString = Printer.post(how, prog, post)
} */

sealed trait Prog {
  def mod: Set[Var]
  def read: Set[Var]
  def breaks: Boolean
  def replace(re: Map[Var, Var]): Prog
}

class ProgList(progs: List[Prog]) {
  def breaks = progs exists (_.breaks)
  def replace(re: Map[Var, Var]) = progs map (_ replace re)
}

case class Block(progs: List[Prog]) extends Prog {
  def mod = Set(progs flatMap (_.mod): _*)
  def read = Set(progs flatMap (_.read): _*)
  def breaks = progs.breaks
  def replace(re: Map[Var, Var]) = Block(progs replace re)
}

case object Break extends Prog {
  def mod = Set()
  def read = Set()
  def breaks = true
  def replace(re: Map[Var, Var]) = this
}

case object Return extends Prog {
  def mod = Set()
  def read = Set()
  def breaks = true
  def replace(re: Map[Var, Var]) = this
}

case class Local(xs: List[Var], rhs: List[Expr]) extends Prog {
  require(xs.nonEmpty, "empty local variable declaration")

  require(
    rhs.isEmpty || xs.length == rhs.length,
    "mismatches between number of variables and initializer in declaration"
  )

  def mod = Set() // Note: all new!
  def read = rhs.free
  def breaks = false
  def replace(re: Map[Var, Var]) = Assign(xs rename re, rhs rename re)
}

case class Assign(xs: List[Var], rhs: List[Expr]) extends Prog {
  require(xs.nonEmpty, "empty assignment")
  require(
    xs.length == rhs.length,
    "mismatches between number of variables and right-hand-side expressions in assignment"
  )

  def mod = Set(xs: _*)
  def read = rhs.free
  def breaks = false
  def replace(re: Map[Var, Var]) = Assign(xs rename re, rhs rename re)
}

case class Spec(xs: List[Var], pre: Expr, post: Expr) extends Prog {
  def mod = xs.toSet
  def read = pre.free ++ (post.free -- mod)
  def breaks = false
  def replace(re: Map[Var, Var]) =
    Spec(xs rename re, pre rename re, post rename re)
}

object Spec extends ((List[Var], Expr, Expr) => Spec) {
  def assert = (pre: Expr) => Spec(Nil, pre, True)
  def assume = (post: Expr) => Spec(Nil, True, post)
}

case class If(test: Expr, left: Prog, right: Prog) extends Prog {
  def mod = left.mod ++ right.mod
  def read = test.free ++ left.read ++ right.read
  def breaks = left.breaks || right.breaks
  def replace(re: Map[Var, Var]) =
    If(test rename re, left replace re, right replace re)
}

object If extends ((Expr, Prog, Option[Prog]) => If) {
  def apply(test: Expr, left: Prog, right: Option[Prog]): If = {
    right match {
      case None        => If(test, left, Skip)
      case Some(right) => If(test, left, right)
    }
  }
}

case class Frame(array: Var, index: Var, phi: Expr) extends Expr.bind[Frame] {
  def bound = Set(index)
  def rename(a: Map[Var, Var], re: Map[Var, Var]) =
    Frame(array, index rename a, phi rename re)
  def subst(a: Map[Var, Var], su: Map[Var, Expr]) =
    Frame(array, index rename a, phi subst su)
}

case class While(
    test: Expr,
    body: Prog,
    term: Expr,
    inv: Expr,
    post: Expr,
    frames: List[Frame]
) extends Prog {
  def mod = body.mod
  def read = test.free ++ body.read
  def breaks = false
  def replace(re: Map[Var, Var]) =
    While(
      test rename re,
      body replace re,
      term rename re,
      inv rename re,
      post rename re,
      frames map (_ rename re)
    )
}

object While
    extends (
        (
            Expr,
            Prog,
            Option[Expr],
            Option[Expr],
            Option[Expr],
            List[Frame]
        ) => While
    ) {
  def apply(
      test: Expr,
      body: Prog,
      term: Option[Expr],
      inv: Option[Expr],
      post: Option[Expr],
      frames: List[Frame]
  ): While = {
    val _term = term getOrElse Zero
    val _inv = inv getOrElse True
    val _post = post getOrElse True
    While(test, body, _term, _inv, _post, frames)
  }
}

/*
case class Call(name: Id, in: List[Expr], out: List[Id]) extends Prog {
  {
    val duplicateOuts = out.groupBy(identity).filter(_._2.size > 1)
    if (duplicateOuts.nonEmpty) {
      throw Error(
        s"The procedure call to $name declares duplicate output parameters ${duplicateOuts.keys.mkString(", ")}"
      )
    }
  }

  def mod = out.toSet
  def read = in.flatMap(_.free).distinct.toSet
  def breaks = false
  def replace(re: Map[Var, Var]) = Call(name, in map (_ rename re), out map (_ rename re))
  override def toString = Printer.call(name, in, out)
}

case class Refines(a: Sort, c: Sort, r: Id) extends Expr {
  override def free: Set[Id] = Set.empty
  override def rename(re: Map[Var, Var]): Expr = {
    ensure(!(re contains r), "Cannot rename refinement")
    this
  }
  override def subst(su: Map[Id, Expr]): Expr = {
    ensure(!(su contains r), "Cannot substitute for refinement identifier")
    this
  }
  override def toString: String = Printer.refines(a, c, r)
}
 */

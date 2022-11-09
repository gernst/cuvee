package cuvee.imp

import cuvee.pure._
import cuvee.util.Name

object Skip extends Block(Nil)

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
  def subst(su: Map[Id, Expr]) = cuvee.undefined
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

  if (rhs.nonEmpty) {
    require(
      xs.length == rhs.length,
      "mismatches between number of variables and initializer in declaration"
    )

    for ((x, e) <- (xs zip rhs)) {
      require(x.typ == e.typ, "ill-typed declaration")
    }
  }

  def mod = Set() // Note: all new!
  def read = rhs.free
  def breaks = false
  def replace(re: Map[Var, Var]) = Local(xs rename re, rhs rename re)
}

object Local extends ((List[Var], Option[List[Expr]]) => Local) {
  def apply(xs: List[Var], rhs: Option[List[Expr]]): Local =
    Local(xs, rhs.getOrElse(Nil))
}

case class Assign(xs: List[Var], rhs: List[Expr]) extends Prog {
  require(xs.nonEmpty, "empty assignment")

  require(
    xs.length == rhs.length,
    "mismatches between number of variables and right-hand-side expressions in assignment"
  )

  for ((x, e) <- (xs zip rhs)) {
    require(x.typ == e.typ, "ill-typed declaration")
  }

  def mod = Set(xs: _*)
  def read = rhs.free
  def breaks = false
  def replace(re: Map[Var, Var]) = Assign(xs rename re, rhs rename re)
}

object Assign extends ((List[Var], List[Expr]) => Assign) {
  def flat(l: Expr, r: Expr): (Var, Expr) = l match {
    case x: Var =>
      (x, r)
    case Select(a, i) =>
      flat(a, Store(a, i, r))
  }

  val flatten = (xs: List[Expr], rhs: List[Expr]) => {
    require(
      xs.length == rhs.length,
      "mismatches between number of variables and right-hand-side expressions in assignment"
    )

    cuvee.undefined
  }
}

case class Spec(xs: List[Var], pre: Expr, post: Expr) extends Prog {
  require(
    pre.typ == Sort.bool,
    "non-boolean precondition in specification statement"
  )
  require(
    post.typ == Sort.bool,
    "non-boolean postcondition in specification statement"
  )

  def mod = xs.toSet
  def read = pre.free ++ (post.free -- mod)
  def breaks = false
  def replace(re: Map[Var, Var]) =
    Spec(xs rename re, pre rename re, post rename re)
}

object Spec extends ((List[Var], Expr, Expr) => Spec) {
  def havoc = (xs: List[Var]) => Spec(xs, True, True)
  def assert = (pre: Expr) => Spec(Nil, pre, True)
  def assume = (post: Expr) => Spec(Nil, True, post)
}

case class If(test: Expr, left: Prog, right: Prog) extends Prog {
  require(
    test.typ == Sort.bool,
    "non-boolean test in if statement"
  )

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
    sum: Expr,
    frames: List[Frame]
) extends Prog {
  require(
    test.typ == Sort.bool,
    "non-boolean test in while statement"
  )
  require(
    term.typ == Sort.int,
    "non-integer decreases clause in while statement"
  )
  require(
    inv.typ == Sort.bool,
    "non-boolean invariant in while statement"
  )
  require(
    sum.typ == Sort.bool,
    "non-boolean summary in while statement"
  )

  def mod = body.mod
  def read = test.free ++ term.free ++ inv.free ++ sum.free ++ body.read
  def breaks = false
  def replace(re: Map[Var, Var]) =
    While(
      test rename re,
      body replace re,
      term rename re,
      inv rename re,
      sum rename re,
      frames map (_ rename re)
    )
}

object While
    extends (
        (
            Expr,
            Option[Expr],
            Spec,
            Prog
        ) => While
    ) {
  def apply(
      test: Expr,
      term_ : Option[Expr],
      spec: Spec,
      body: Prog
  ): While = {
    val term = term_ getOrElse Zero
    val Spec(xs, inv, sum) = spec
    require(xs.isEmpty, "modifies annotation for loops not supported")
    While(test, body, term, inv, sum, frames = Nil)
  }
}

case class Call(name: Name, in: List[Expr], out: List[Var]) extends Prog {
  def dup = out.groupBy(identity).filter(_._2.size > 1)
  require(dup.nonEmpty, "procedure call " + name + " has duplicate outputs " + dup)

  def mod = out.toSet
  def read = in.free
  def breaks = false
  def replace(re: Map[Var, Var]) =
    Call(name, in rename re, out rename re)
}

/*
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

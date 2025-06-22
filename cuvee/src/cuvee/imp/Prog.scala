package cuvee.imp

import cuvee.pure._
import cuvee.util
import cuvee.sexpr
import cuvee.util.Name

object Skip extends Block(Nil)

sealed trait Modality extends ((List[Prog], Expr) => Expr) {
  def spec(xs: List[Var], pre: Expr, post: Expr): Expr
  def split(cond: Expr, left: Expr, right: Expr): Expr

  def apply(progs: List[Prog], post: Expr) = {
    Post(this, Block(progs), post)
  }

  def unapply(expr: Post) =
    expr match {
      case Post(how, prog, post) if how == this =>
        Some((prog, post))
      case Post(how, prog, post) if how == this =>
        Some((prog, post))
      case _ =>
        None
    }
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
  def vars: Set[Var]
  def mod: Set[Var]
  def read: Set[Var]
  def local: Set[Var]
  def funs: Set[Fun]
  def breaks: Boolean
  def replace(re: Map[Var, Var]): Prog
}

class ProgList(progs: List[Prog]) {
  def mod: Set[Var] = progs match {
    case Nil =>
      Set()
    case prog :: rest =>
      prog.mod ++ (rest.mod -- prog.local)
  }

  def read: Set[Var] = progs match {
    case Nil =>
      Set()
    case prog :: rest =>
      prog.read ++ (rest.read -- (prog.local ++ prog.mod))
  }

  def vars: Set[Var] =
    Set(progs flatMap (_.vars): _*)

  def local: Set[Var] =
    Set(progs flatMap (_.local): _*)

  def funs: Set[Fun] =
    Set(progs flatMap (_.funs): _*)

  def breaks =
    progs exists (_.breaks)

  def replace(re: Map[Var, Var]) =
    progs map (_ replace re)
}

object Prog {

  def liftLocals(
      avoid: Set[Var],
      prog: Prog
  ): (List[Var], Prog) = {
    liftLocals(avoid, List(prog), Nil) match {
      case (xs_, List(prog)) => (xs_, prog)
      case (xs_, progs)      => (xs_, Block(progs))
    }
  }

  def liftLocals(
      avoid: Set[Var],
      progs: List[Prog],
      cont: List[List[Prog]]
  ): (List[Var], List[Prog]) = {
    progs match {
      case Nil =>
        cont match {
          case Nil =>
            (Nil, Nil)

          case todo :: cont =>
            liftLocals(avoid, todo, cont)
        }

      case Local(xs, Nil) :: rest =>
        val zs = avoid & xs.toSet
        val re = Expr.fresh(zs)
        val xs_ = xs rename re
        val rest_ = rest replace re
        val (ys_, progs_) = liftLocals(avoid ++ xs_, rest_, cont)
        (xs_ ++ ys_, progs_)

      case Local(xs, rhs) :: rest =>
        val zs = avoid & xs.toSet
        val re = Expr.fresh(zs)
        val xs_ = xs rename re
        val asg_ = Assign(xs_, rhs)
        val rest_ = rest replace re
        val (ys_, progs_) = liftLocals(avoid ++ xs_, rest_, cont)
        (xs_ ++ ys_, asg_ :: progs_)

      case Block(progs) :: rest =>
        liftLocals(avoid, progs, rest :: cont)

      case If(test, left, right) :: rest =>
        val (xs1, left_) = liftLocals(avoid, left)
        val (xs2, right_) = liftLocals(avoid, right)
        val (ys_, progs_) = liftLocals(avoid ++ xs1 ++ xs2, rest, cont)
        val if_ = If(test, left_, right_)
        (xs1 ++ xs2 ++ ys_, if_ :: progs_)

      case While(test, body, term, pre, post, frames) :: rest =>
        val (xs_, body_) = liftLocals(avoid, body)
        val (ys_, progs_) = liftLocals(avoid ++ xs_, rest, cont)
        val while_ = While(test, body_, term, pre, post, frames)
        (xs_, while_ :: progs_)

      case prog :: rest =>
        val (xs_, progs_) = liftLocals(avoid, rest, cont)
        (xs_, prog :: progs_)
    }
  }
}

case class Note(prog: Prog, attrs: sexpr.Attrs) extends Prog {
  def vars = prog.vars
  def mod = prog.mod
  def read = prog.read
  def local = prog.local
  def funs = prog.funs
  def breaks = prog.breaks

  def replace(re: Map[Var, Var]) =
    Note(prog replace re, attrs)
}

case class Block(progs: List[Prog]) extends Prog {
  def vars = progs.vars
  def mod = progs.mod
  def read = progs.read
  def local = Set() // no *exposed* locals
  def funs = progs.funs
  def breaks = progs.breaks
  def replace(re: Map[Var, Var]) = Block(progs replace re)
}

case object Break extends Prog {
  def vars = Set()
  def mod = Set()
  def read = Set()
  def local = Set()
  def funs = Set()
  def breaks = true
  def replace(re: Map[Var, Var]) = this
}

case object Continue extends Prog {
  def vars = Set()
  def mod = Set()
  def read = Set()
  def local = Set()
  def funs = Set()
  def breaks = true
  def replace(re: Map[Var, Var]) = this
}

case object Return extends Prog {
  def vars = Set()
  def mod = Set()
  def read = Set()
  def local = Set()
  def funs = Set()
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
      require(x.typ == e.typ, "ill-typed declaration: " + x + " := " + e)
    }
  }
  def vars = rhs.free
  def mod = Set() // Note: all new!
  def read = rhs.free
  def local = xs.toSet
  def funs = rhs.funs
  def breaks = false
  def replace(re: Map[Var, Var]) =
    Local(xs rename re, rhs rename re)
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
    require(x.typ == e.typ, "ill-typed assignment: " + x + " := " + e)
  }

  def vars = rhs.free ++ xs
  def mod = Set(xs: _*)
  def read = rhs.free
  def local = Set()
  def funs = rhs.funs
  def breaks = false
  def replace(re: Map[Var, Var]) = Assign(xs rename re, rhs rename re)
}

object Assign extends ((List[Var], List[Expr]) => Assign) {
  def main(args: Array[String]): Unit = {
    val i = Var("i", Sort.int)
    val j = Var("j", Sort.int)
    val k = Var("k", Sort.int)

    val v = Var("v", Sort.int)

    val a = Var("a", Sort.array(Sort.int, Sort.int))
    val b = Var("b", Sort.array(Sort.int, Sort.array(Sort.int, Sort.int)))
    val c = Var("c", Sort.array(Sort.int, Sort.array(Sort.int, Sort.array(Sort.int, Sort.int))))

    val (l1, r1) = nested(Select(a, List(i)), v)
    val (l2, r2) = nested(Select(b, List(i, j)), v)
    val (l3, r3) = nested(Select(c, List(i, j, k)), v)

    println(l1 + " := " + r1)
    println(l2 + " := " + r2)
    println(l3 + " := " + r3)

    val (l1_, r1_) = flatten(l1, r1)
    val (l2_, r2_) = flatten(l2, r2)
    val (l3_, r3_) = flatten(l3, r3)

    println(l1_ + " := " + r1_)
    println(l2_ + " := " + r2_)
    println(l3_ + " := " + r3_)
  }

  def nested(l: Expr, r: Expr): (Var, Expr) = l match {
    case x: Var =>
      (x, r)
    case Select(a, i) =>
      nested(a, Store(a, i, r))
  }

  def flatten(l: Expr, r: Expr): (Expr, Expr) = r match {
    case Store(`l`, i, r_) =>
      flatten(Select(l, i), r_)

    case _ =>
      (l, r)
  }

  // x[i] := v
  // x := x[i:=v]

  // x[i][j] := v
  // x := x[i:=x[i][j:=v]]

  // x[i][j][k] := v
  // x := x[i:=x[i][j:=x[i][j][k:=v]]]

  def from: ((Expr, Expr) => Assign) = { case (l, r) =>
    val (l_, r_) = nested(l, r)
    Assign(List(l_), List(r_))
  }

  def froms: ((List[Expr], List[Expr]) => Assign) = { case (lhs, rhs) =>
    val asgs =
      for ((l, r) <- lhs zip rhs)
        yield nested(l, r)
    val (lhs_, rhs_) = asgs.unzip
    Assign(lhs_, rhs_)
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
    "non-boolean precondition in specification statement: " + pre
  )
  require(
    post.typ == Sort.bool,
    "non-boolean postcondition in specification statement: " + post
  )
  def vars = pre.free ++ post.free ++ xs
  def mod = xs.toSet
  def read = pre.free ++ (post.free -- xs)
  def funs = pre.funs ++ post.funs
  def local = Set()
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

  def vars = test.free ++ left.vars ++ right.vars
  def mod = left.mod ++ right.mod
  def read = test.free ++ left.read ++ right.read
  def funs = test.funs ++ left.funs ++ right.funs
  def local = left.local ++ right.local
  def breaks = left.breaks || right.breaks
  def replace(re: Map[Var, Var]) =
    If(test rename re, left replace re, right replace re)
}

object If extends ((Expr, Prog, Option[Prog]) => If) {

  def apply(test: Expr, left: Prog): If = {
    If(test, left, Skip)
  }

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

  def vars = test.free ++ body.vars
  def mod = body.mod
  def read = test.free ++ term.free ++ inv.free ++ sum.free ++ body.read
  def funs = test.funs ++ term.funs ++ inv.funs ++ sum.funs ++ body.funs
  def local = body.local
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

object While extends ((Expr, Option[Expr], Spec, Prog) => While) {

  def apply(test: Expr, body: Prog): While = {
    While(test, body, Zero, True, True, Nil)
  }

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
  require(dup.isEmpty, "procedure call " + name + " has duplicate outputs " + dup)

  def vars = in.free ++ out.free
  def mod = out.toSet
  def read = in.free
  def funs = in.funs
  def local = Set()
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

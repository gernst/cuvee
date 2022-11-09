package cuvee.pure

trait Assoc {
  def reduce[A](xs: Iterable[A], f: (A, A) => A): A
  def fold[A](xs: Iterable[A], z: A, f: (A, A) => A): A
}

object Assoc {
  // Note: nested to avoid name clashes with Either cases
  case object left extends Assoc {
    def reduce[A](xs: Iterable[A], f: (A, A) => A): A =
      xs.reduceLeft(f)
    def fold[A](xs: Iterable[A], z: A, f: (A, A) => A): A =
      xs.foldLeft(z)(f)
  }

  case object right extends Assoc {
    def reduce[A](xs: Iterable[A], f: (A, A) => A): A =
      xs.reduceRight(f)
    def fold[A](xs: Iterable[A], z: A, f: (A, A) => A): A =
      xs.foldRight(z)(f)
  }
}

object Sugar {
  class binder(val quant: Quant, val typ: Type) extends ((List[Var], Expr) => Expr) {
    def unapply(expr: Bind) =
      expr match {
        case Bind(`quant`, formals, body, `typ`) => Some((formals, body))
        case _                                   => None
      }

    def apply(formals: List[Var], body: Expr) = {
      val formals_ = formals filter body.free
      if (formals_.isEmpty) body
      else Bind(quant, formals, body, typ)
    }
  }

  class unary(val fun: Fun) extends (Expr => Expr) {
    def unapply(expr: Expr) =
      expr match {
        case App(inst, List(arg)) if inst.fun == fun =>
          Some(arg)
        case _ =>
          None
      }

    def apply(arg: Expr) = {
      App(fun, List(arg))
    }
  }

  class pointwise(fun: Fun) extends unary(fun) {
    def apply(exprs: List[Expr]) = {
      exprs map this
    }
  }

  class binary(val fun: Fun) extends ((Expr, Expr) => Expr) {
    def unapply(expr: Expr) =
      expr match {
        case App(inst, List(arg1, arg2)) if inst.fun == fun =>
          Some((arg1, arg2))
        case _ =>
          None
      }

    def apply(arg1: Expr, arg2: Expr): Expr = {
      App(fun, List(arg1, arg2))
    }
  }

  class ternary(val fun: Fun) extends ((Expr, Expr, Expr) => Expr) {
    def unapply(expr: Expr) =
      expr match {
        case App(inst, List(arg1, arg2, arg3)) if inst.fun == fun =>
          Some((arg1, arg2, arg3))
        case _ =>
          None
      }

    def apply(arg1: Expr, arg2: Expr, arg3: Expr): Expr = {
      App(fun, List(arg1, arg2, arg3))
    }
  }

  class associative(fun: Fun, val assoc: Assoc) extends binary(fun) {
    def apply(args: List[Expr]): Expr =
      assoc.reduce(args, this)

    def flatten(expr: Expr): List[Expr] =
      expr match {
        case App(inst, List(arg1, arg2)) if inst.fun == fun && assoc == Assoc.left =>
          flatten(arg1) ++ List(arg2)
        case App(inst, List(arg1, arg2)) if inst.fun == fun && assoc == Assoc.right =>
          List(arg1) ++ flatten(arg2)
        case _ =>
          List(expr)
      }
  }

  case class commutative(val fun: Fun, val neutral: Expr, val assoc: Assoc)
      extends (List[Expr] => Expr) {
    def flatten(exprs: List[Expr]): List[Expr] =
      exprs flatMap flatten

    def flatten(expr: Expr): List[Expr] =
      expr match {
        case App(inst, args) if inst.fun == fun =>
          flatten(args)
        // Note: this case causes And(phis) with empty phi,
        //       which is not necessarily understood by solvers
        // case `neutral` =>
        //   Nil
        case _ =>
          List(expr)
      }

    def apply(arg1: Expr, arg2: Expr): Expr = {
      App(fun, List(arg1, arg2))
    }

    def apply(args: List[Expr]): Expr =
      args match {
        case Nil       => neutral
        case List(arg) => arg
        case _         => assoc.reduce(args, apply)
      }

    def unapply(expr: Expr) =
      expr match {
        case App(inst, args) if inst.fun == fun =>
          Some(flatten(args))
        case _ =>
          None
      }
  }
}

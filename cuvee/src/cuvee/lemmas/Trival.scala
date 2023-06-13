package cuvee.lemmas

import cuvee.pure._

object Trivial {
  def identity(df: Def, args: List[Expr]): List[Expr] = {
    val Def(f, cases) = df

    val ok = cases forall {
      case C(List(Zero), Nil, Zero) =>
        true
      case C(List(Succ(m)), Nil, Succ(n)) if m == n =>
        true
      case C(List(Succ(m)), Nil, Succ(App(Inst(`f`, _), List(n)))) if m == n =>
        true
      case C(List(x: Var), Nil, y) if x == y => // TODO: cannot recognize complete guard splits
        true
      case C(List(App(c, xs)), Nil, App(d, es)) if c == d => // TODO: assumes c is a constructor
        (xs zip es) forall {
          case (x: Var, y) if x == y =>
            true // argument passed unchanged
          case (x: Var, App(Inst(`f`, _), List(y))) if x == y =>
            true // argument passed through recursive call
          case cs =>
            false
        }
      case cs =>
        false
    }

    if (ok) {
      assert(args.length == 1)
      List(args(0))
    } else {
      List()
    }
  }

  def constant(df: Def, args: List[Expr]): List[Expr] = {
    val Def(f, cases) = df
    val static = df.staticArgs

    val stuff = cases map {
      case C(args, guard, x: Var) => // x is static
        val ok = static find { (i: Int) => args(i) == x }
        ok match {
          case None =>
            (false, None)
          case Some(i) =>
            (true, Some(i))
        }
      case C(args, guard, App(Inst(`f`, _), _)) => // tail-recursive
        (true, None)
      case cs =>
        (false, None)
    }

    val (oks, is_) = stuff.unzip
    val ok = oks.forall(b => b)
    val is = is_.flatten

    (ok, is) match {
      case (true, List(i)) =>
        List(args(i))
      case _ =>
        List()
    }
  }

// def maybeNeutralAt()

//   def withNeutral(df: Def, args: List[Expr]): List[(List[Expr], Expr)] = {
//     val Def(f, cases) = df
//     val static = df.staticArgs

//     val ostuffk = cases map {
//       case C(args, Nil, x: Var) =>
//         val ok = static find { (i: Int) => args(i) == x }

//         ok match {
//           case None =>
//             (false, None)
//           case Some(i) =>
//             (true, Some(i))
//         }

//       case C(List(App(c, xs)), Nil, App(d, es)) if c == d => // TODO: assumes c is a constructor
//         (xs zip es) forall {
//           case (x: Var, y) if x == y =>
//             true // argument passed unchanged
//           case (x: Var, App(Inst(`f`, _), List(y))) if x == y =>
//             true // argument passed through recursive call
//           case cs =>
//             false
//         }
//       case cs =>
//         false
//     }

//     // if (ok) {
//     //   assert(args.length == 1)
//     //   List(args(0))
//     // } else {
//     //   List()
//     // }

//     ???
//   }
}

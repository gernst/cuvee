package cuvee.lemmas

import cuvee.error
import cuvee.State
import cuvee.util.Name
import cuvee.pure._
import cuvee.smtlib._

case class C(args: List[Expr], guard: List[Expr], body: Expr) extends Expr.bind[C] {
  def typ = body.typ
  def flat(self: Fun) = this
  def bound = args.free

  require(!(guard contains True), "guard contains " + True)
  require(!(guard contains False), "guard contains " + False)

  require(body.free subsetOf args.free, this + " does not bind: " + (body.free -- args.free))
  require(guard.free subsetOf args.free, this + " does not bind: " + (guard.free -- args.free))

  def replace(f: Fun, g: Fun) = {
    C(args replace (f,g), guard replace (f,g), body replace (f,g))
  }

  def rename(a: Map[Var, Var], re: Map[Var, Var]) = {
    C(args rename a, guard rename re, body rename re)
  }

  def subst(a: Map[Var, Var], su: Map[Var, Expr]) = {
    C(args rename a, guard subst su, body subst su)
  }

  def inst(su: Map[Param, Type]) = {
    C(args inst su, guard inst su, body inst su)
  }

  def rule(self: Fun): Rule = {
    Rule(App(self, args), body, And(guard))
  }

  def axiom(self: Fun) = {
    val xs = args.free.toList
    Clause(xs, guard, Eq(App(self, args), body))
  }

  def isRecursive(fun: Fun): Boolean =
    fun in body

  def countRecursive(fun: Fun): Int = body.reduce[Int](_ + _) {
    case App(Inst(`fun`, _), args) =>
      1
    case _ =>
      0
  }

  def isHoistedBase: Boolean = body match {
    case x: Var =>
      args contains x
    case _ =>
      false
  }

  def isTailRecursive(fun: Fun): Boolean =
    body match {
      case App(Inst(`fun`, _), args) =>
        true
      case _ =>
        false
    }

  override def toString = {
    if (guard.isEmpty)
      args.mkString("case ", ", ", "") + "  = " + body
    else
      args.mkString("case ", ", ", " if ") + guard.mkString(
        " /\\ "
      ) + "  = " + body
  }
}

case class Def(fun: Fun, cases: List[C]) {
  for (cs <- cases) {
    require(
      fun.args == cs.args.types,
      "type mismatch: " + fun + " applied to " + cs.args
    )
    require(
      fun.res == cs.typ,
      "type mismatch: " + fun + " in case " + cs + ": " + cs.typ
    )
  }

  def params = fun.params
  def args = fun.args
  def typ = fun.res

  def rules =
    cases map (_ rule fun)

  def map(f: C => C): Def =
    Def(fun, cases map f)

  def cmds =
    decl :: axioms

  def decl = {
    val Fun(name, params, args, res) = fun
    DeclareFun(name, params, args, res)
  }

  def axioms = {
    cases map (cs => Assert(cs axiom fun))
  }

  def isMatchingPosition(pos: Int): Boolean = {
    cases exists { case C(args, guard, body) =>
      val arg = args(pos)
      arg.isInstanceOf[App] || arg.isInstanceOf[Lit]
    }
  }

  // object Norm {
  //   def unapply(c: C) = {
  //     val C(args, guard, body) = c
  //     val ((d, r), (as, bs, cs)) = Split.split(fun, body)
  //     Some((args, guard, as, bs, cs, d))
  //   }
  // }

  def rename(re: Name => Name): Def = {
    val fun_ = fun rename re
    val cases_ =
      for (C(args, guard, body) <- cases)
        yield {
          val body_ = body bottomup {
            case App(Inst(`fun`, su), args) =>
              App(Inst(fun_, su), args)
            case expr =>
              expr
          }

          C(args, guard, body_)
        }

    Def(fun_, cases_)
  }

  def rewrite(rules: Map[Fun, List[Rule]]) = {
    val cases_ =
      for (C(args, guard, body) <- cases)
        yield {
          val guard_ = Rewrite.rewrites(guard, rules)
          val body_ = Rewrite.rewrite(body, rules)
          C(args, guard_, body_)
        }

    Def(fun, cases_)
  }

  def simplify(rules: Map[Fun, List[Rule]], constrs: Set[Fun]) = {
    val cases_ =
      for (C(args, guard, body) <- cases)
        yield {
          val guard_ = Simplify.simplify(guard, rules, constrs)
          val body_ = Simplify.simplify(body, rules, constrs)
          C(args, guard_ filterNot(_ == True), body_)
        }

    Def(fun, cases_)
  }

  override def toString = {
    fun + cases.mkString("\n", "\n", "")
  }

  def staticArgs: List[Int] = {
    val (as, _) = staticAndNonstaticArgs
    as
  }

  def staticAndNonstaticArgs: (List[Int], List[Int]) = {
    val is = 0 until fun.args.length
    is.toList.partition { i: Int =>
      cases forall { case C(args, guard, body) =>
        args(i) match {
          // ensure that static arguments are are always variables
          case a: Var => Def.isStatic(fun, i, a, body)
          case _      => false
        }

      }
    }
  }

  def usedArgs: List[Int] = {
    val(xs, ys) = usedAndUnusedArgs
    xs
  }

  def usedAndUnusedArgs: (List[Int], List[Int]) = {
    val is = 0 until fun.args.length
    is.toList.partition { i: Int =>
      cases exists { case C(args, guard, body) =>
        args(i) match {
          case x: Var =>
            (x in guard) || Def.isUsed(fun, i, x, body)
          case _ =>
            true
        }
      }
    }
  }

  def isRecursive = {
    cases exists (_ isRecursive fun)
  }
}

object Def {
  def isUsed(f: Fun, i: Int, x: Var, e: Expr): Boolean = e match {
    case _: Lit => false
    case y: Var => x == y

    case App(Inst(`f`, _), args) =>
      args.zipWithIndex.exists { case (arg, j) =>
        j != i && isUsed(f, i, x, arg)
      }

    case App(_, args) =>
      args.exists(isUsed(f, i, x, _))
  }
  
  def isStatic(f: Fun, i: Int, a: Var, e: Expr): Boolean = e match {
    case _: Lit => true
    case y: Var => true

    case App(Inst(`f`, _), args) =>
      args(i) == a

    case App(_, args) =>
      args.forall(isStatic(f, i, a, _))
  }

  import scala.util.hashing.MurmurHash3
  val paramSeed = "Param".hashCode
  val varSeed = "Var".hashCode

  def hash(t: Type): Int = t match {
    case p: Param =>
      paramSeed
    case Sort(con, args) =>
      MurmurHash3.orderedHash(hash(args), con.hashCode())
  }

  def hash(t: Type, seed: Int): Int = {
    MurmurHash3.mix(hash(t), seed)
  }

  def hash(ts: List[Type]): List[Int] = {
    ts map (hash(_))
  }

  // weak hash function that captures the structure
  // but not the actual computation
  // it forgets variable names,
  // function name and order of arguments for recursive calls,
  // as well as all type instances
  def hash(f: Set[Fun], e: Expr): Int = e match {
    case x: Var =>
      varSeed
    case l: Lit =>
      l.hashCode
    case App(Inst(g, _), args) if f contains g =>
      MurmurHash3.unorderedHash(hash(f, args))
    case App(Inst(g, _), args) =>
      MurmurHash3.orderedHash(hash(f, args), g.name.hashCode)
  }

  def hash(f: Set[Fun], es: List[Expr]): List[Int] = {
    es map (hash(f, _))
  }

  def hashs(f: Set[Fun], es: List[Expr]): Int = {
    MurmurHash3.orderedHash(es map (hash(f, _)))
  }

  def hash(f: Set[Fun], c: C): Int = c match {
    case C(args, guard, body) =>
      val h1 = hash(f, body)
      val h2 = MurmurHash3.unorderedHash(hash(f, args), h1)
      val h3 = MurmurHash3.unorderedHash(hash(f, guard), h2)
      h3
  }

  def hash(df: Def): Int = df match {
    case Def(f, cases) =>
      MurmurHash3.unorderedHash(cases map (hash(Set(f), _)))
  }
}

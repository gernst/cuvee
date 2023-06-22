package cuvee.lemmas

import cuvee.pure._
import cuvee.util.Name
import cuvee.smtlib.Model
import cuvee.smtlib.Solver
import cuvee.State
import cuvee.backend.Builtin
import cuvee.smtlib.Unsat

object Deaccumulate {
  // case object CannotDeaccumulate extends Exception
  var debug = false

  var heuristics = 0

  class Cond(val prio: Int)
  case class N(o: Fun, b: Fun) extends Cond(0)
  case class D(f: Fun, args: List[Var], body: Expr) extends Cond(1)
  case class A(l: Expr, r: Expr, g: Expr) extends Cond(2)
  case class G(f: Fun, args: List[Var], body: Expr) extends Cond(3)
  case class B(formals: List[Var], b: Fun, args: List[Var], l: Expr, r: Expr, g: Expr)
      extends Cond(4)

  def mayDeaccumulateAt(df: Def) = if (df.isRecursive) {
    for ((_, pos) <- df.fun.args.zipWithIndex if isAccumulator(df, pos))
      yield pos
  } else {
    Nil
  }

  // this is partly a heuristic which arguments may be worthy of deaccumulation;
  // the requirement that the argument is matched as a variable only is needed
  def isAccumulator(df: Def, pos: Int) = {
    df.cases forall { case (C(args, guard, body)) =>
      args(pos) match {
        case x: Var =>
          val (body_, recs) = abstracted(df.fun, body)
          // throw new Exception("insight is that the hoisted base cases are dependent on accumulators, so that it makes sense to consider *all* arguments introduced via fusion, and get rid of them by restricting which parameters the new body and guards may use")
          !(x in guard) && !(recs exists { case (y, args) => (x in (args removed pos)) })
        case _ =>
          false
      }
    }
  }

  def deaccumulated(name: Name, pos: Int) = {
    val Name(str, None) = name
    Name(str + "^" + pos, None)
  }

  def deaccumulateAt(
      df: Def,
      args: List[Expr],
      pos: Int,
      static: List[Int]
  ) = {
    val Def(f, cases) = df
    val Fun(name, params, types, res) = f

    val name_ = deaccumulated(name, pos)
    val params_ = params
    val types_ = types removed pos
    val f_ = Fun(name_, params_, types_, res)

    val static_ = static filterNot (_ == pos)
    val args_ = static_ map args
    // val XS = Expr.vars("x", args)
    // val ZS = static_ map XS

    val typ = types(pos)
    val ⊕ = Fun("oplus!", params, List(res, typ) ++ args_.types, res)

    val stuff =
      for ((cs @ C(args, guard, body), j) <- cases.zipWithIndex)
        yield {
          val u @ Var(_, _) = args(pos)
          assert(!(u in guard))

          val args_ = args removed pos
          // val xs = args.free.toList
          val xs_ = args_.free.toList

          val (lhs, recs) = abstracted(f, body)
          val (ys, arglists) = recs.unzip

          val zs = static_ map args collect { case z: Var =>
            z
          }

          val acc =
            for ((y, args) <- recs)
              yield (y, App(⊕, List(y, args(pos)) ++ zs))

          val su = Expr.subst(acc)

          val arglists_ =
            for ((y, args) <- recs)
              yield App(f_, args removed pos)

          // if all other variables are static -> can refer to these in oplus
          if (ys.isEmpty && (u in body) && ((body.free - u) subsetOf zs.toSet)) {
            val n = Name("body", Some(j))
            val b = Fun(n, params, Nil, res)

            val m = Name("odot", Some(j))

            // TODO: add static global args to oplus
            val ⊙ = Fun(m, params, List(res, res), res)
            val y = Expr.fresh("y", res)
            val z = Expr.fresh("z", res)

            val body_ = b()

            // TODO: rename static globals in the lifted body
            val eq1 = Rule(⊙(body_, z), z)
            val eq2 = Rule(App(⊕, List(y, u) ++ zs), ⊙(y, body))
            val cs_ = C(args_, guard, body_)

            (cs_, List(b, ⊙), (List(eq1, eq2), List(N(⊙, b), D(⊕, List(y, u) ++ zs, ⊙(y, body)))))

          } /* else if (
            false && ys.nonEmpty && (static contains pos) && (body_.free subsetOf args_.free)
          ) {
            // this is a heuristic that does not work for deaccumulating reverse.append
            // ra [] ys = reverse ys
            // ra (x:xs) ys = snoc (ra xs ys) x
            // println(lhs)
            // println(su_)
            // println(args + " and " + args_)
            val cs_ = C(args_, guard, body_)
            // cannot rely on facts about the guard as it may refer to non-static information here
            val eq = Rule(App(⊕, List(lhs, u) ++ zs), lhs subst su /*, And(guard) */ )

            // promote through a body without compensating for the accumulator
            (cs_, List(), (List(eq), List(A(App(⊕, List(lhs, u) ++ zs), lhs subst su, And(guard)))))
          } */
          else {
            val n = Name("phi" + j)
            val b = Fun(n, params, xs_.types ++ ys.types, res)

            val body_ = App(b, xs_ ++ arglists_)
            val cs_ = C(args_, guard, body_)

            val rhs = App(⊕, List(App(b, xs_ ++ ys), u) ++ zs)
            val eq = Rule(rhs, lhs subst su, And(guard))

            val su_ = Expr.subst(ys, arglists_)
            val orig_ = lhs subst su_

            val vs = (u :: xs_ ++ ys ++ zs).distinct

            val conds =
              if (recs.nonEmpty && (static contains pos) && (orig_.free subsetOf args_.free)) {
                // offer a guess here that the body will remain unchanged, not useful for reverse:0:append
                val guess = G(b, xs_ ++ ys, lhs)
                val cond = B(vs, b, xs_ ++ ys, rhs, lhs subst su, And(guard))
                List(guess, cond)
              } else if (recs.length == 1 && u.typ == res) { // direct accumulator
                val List((y, args)) = recs
                val acc = args(pos) subst Map(u -> y)
                val guess = G(b, xs_ ++ ys, acc)
                val cond = B(vs, b, xs_ ++ ys, rhs, lhs subst su, And(guard))
                List(guess, cond)
              } else {
                val cond = B(vs, b, xs_ ++ ys, rhs, lhs subst su, And(guard))
                List(cond)
              }

            (cs_, List(b), (List(eq), conds))
          }
        }

    val (cases_, bs, eqs_conds) = stuff.unzip3
    val (eqs, conds) = eqs_conds.unzip

    val df_ = Def(f_, cases_)

    val rhs = App(⊕, List(App(f_, args removed pos), args(pos)) ++ args_)

    (df_, rhs, ⊕, ⊕ :: bs.flatten, eqs.flatten, conds.flatten)
  }

  def abstracted(
      f: Fun,
      exprs: List[Expr]
  ): (List[Expr], List[(Var, List[Expr])]) = {
    val stuff = exprs map (abstracted(f, _))
    val (exprs_, xs) = stuff.unzip
    (exprs_, xs.flatten)
  }

  def abstracted(f: Fun, expr: Expr): (Expr, List[(Var, List[Expr])]) = {
    expr match {
      case x: Var =>
        (x, Nil)
      case l: Lit =>
        (l, Nil)
      case App(Inst(`f`, _), args) =>
        var z = Expr.fresh("y", f.res)
        (z, List(z -> args))
      case App(inst, args) =>
        val (args_, xs) = abstracted(f, args)
        (App(inst, args_), xs)
    }
  }

  def solve(
      solver: Solver,
      consts: LazyList[Expr],
      funs: LazyList[Fun],
      datatypes: Map[Name, Datatype],
      unknowns: Set[Fun],
      conds: List[Cond],
      rules: Map[Fun, List[Rule]] = Map()
  ): LazyList[(Set[Fun], List[Rule], Map[Fun, List[Rule]])] = {
    val neutrals = conds collect { case c: N => c }
    val defs = conds collect { case c: D => c }
    val easy = conds collect { case c: A => c }
    assert(easy.isEmpty, "all easy cases should be presented as guesses instead")
    val guess = conds collect { case c: G => c }
    val hard = conds collect { case c: B => c }

    // require(neutrals.nonEmpty)

    // if (defs.length > 1) {
    //   for (d <- defs)
    //     println("  " + d)
    // }
    // require(defs.length < 2, "heuristic leads to ambiguous abbreviations")

    solve(
      solver,
      consts,
      funs,
      datatypes,
      unknowns,
      neutrals,
      defs,
      easy,
      guess,
      hard,
      rules
    )
  }

  // assumes that conds is sorted in some reasonable order (e.g. prio)
  def solve(
      solver: Solver,
      consts: LazyList[Expr],
      funs: LazyList[Fun],
      datatypes: Map[Name, Datatype],
      unknowns: Set[Fun],
      neutrals: List[N],
      defs: List[D],
      easy: List[A],
      guess: List[G],
      hard: List[B],
      rules: Map[Fun, List[Rule]]
  ): LazyList[(Set[Fun], List[Rule], Map[Fun, List[Rule]])] =
    (neutrals, defs, easy, guess, hard) match {
      case (Nil, Nil, Nil, Nil, Nil) =>
        LazyList((unknowns, Nil, rules))

      case (N(o, b) :: rest, _, _, _, _) =>
        require(unknowns contains o, "already solved for " + o)
        require(unknowns contains b, "already solved for " + b)

        val rulelists =
          for (op <- neutral((o.args, o.res)))
            yield {
              val xs = Expr.vars("x", o.args)
              val (eq1, eq2) = op(o, b, xs)
              if (debug) {
                println("  neutral: " + eq1)
                println("  neutral: " + eq2)
              }
              rules + (b -> List(eq1)) + (o -> List(eq2))
            }

        if (rulelists.isEmpty)
          if (debug)
            println("no known neutral element for: " + o)

        for (
          rules_ <- rulelists;
          result <- solve(
            solver,
            consts,
            funs,
            datatypes,
            unknowns - o - b,
            rest,
            defs,
            easy,
            guess,
            hard,
            rules_
          )
        )
          yield result

      case (Nil, D(f, args, body) :: rest, _, _, _) if unknowns contains f =>
        require(!(rules contains f), "unexpected existing rule for " + f)

        val eq = Rule(App(f, args), body)
        // if (debug)
        //   println("  defining: " + eq)
        val rules_ = rules + (f -> List(eq))
        solve(solver, consts, funs, datatypes, unknowns - f, Nil, rest, easy, guess, hard, rules_)

      case (Nil, D(f, args, body) :: rest, _, _, _) =>
        val cond = A(App(f, args), body, True)
        solve(
          solver,
          consts,
          funs,
          datatypes,
          unknowns,
          Nil,
          rest,
          cond :: easy,
          guess,
          hard,
          rules
        )

      case (Nil, Nil, (cond @ A(lhs, rhs, guard)) :: rest, _, _) =>
        // println("  using rules")
        // for((_, eqs) <- rules; eq <- eqs)
        //   println("    " + eq)
        // println("consider: " + eq)
        // if (debug)

        val success =
          try {
            val lhs_ = Simplify.simplify(lhs, rules, Set())
            val rhs_ = Simplify.simplify(rhs, rules, Set())
            val guard_ = Simplify.simplify(guard, rules, Set())

            val xs = lhs_.free ++ rhs_.free ++ guard_.free
            val phi = Forall(xs.toList, Imp(guard_, Eq(lhs_, rhs_)))
            if (debug)
              print("proving:  " + phi + " ... ")

            val s = lhs_ == rhs_
            val a = s // || solver.isTrue(phi)
            val b = a // || cuvee.a.Prove.holdsByInduction(solver, phi, datatypes)
            if (b && !s && !a) println("proved by induction: " + phi)
            b
          } catch {
            case e: cuvee.smtlib.Error =>
              if (debug)
                println(e.info)
              false
            case e: Exception =>
              if (debug)
                e.printStackTrace()
              false
          }

        if (success) {
          if (debug)
            println(" success.")
          solve(solver, consts, funs, datatypes, unknowns, Nil, Nil, rest, guess, hard, rules)
        } else {
          if (debug)
            println(" unknown.")

          // for (
          //   (unknowns_, todo, rules) <- solve(
          //     solver,
          //     consts,
          //     funs,
          //     unknowns,
          //     Nil,
          //     Nil,
          //     rest,
          //     guess,
          //     hard,
          //     rules
          //   )
          // )
          //   yield (unknowns_, eq_ :: todo, rules)
          LazyList()
        }

      case (Nil, Nil, Nil, guess, B(xs, b, _, lhs, rhs, guard) :: rest) if !(unknowns contains b) =>
        solve(
          solver,
          consts,
          funs,
          datatypes,
          unknowns,
          Nil,
          Nil,
          List(A(lhs, rhs, guard)),
          guess,
          rest,
          rules
        )

      case (Nil, Nil, Nil, G(f, args, body) :: rest, hard) if unknowns contains f =>
        require(!(rules contains f), "unexpected existing rule for " + f)

        val eq = List(Rule(App(f, args), body))
        if (debug)
          println("  guessing: " + eq)
        val rules_ = rules + (f -> eq)
        val first =
          solve(solver, consts, funs, datatypes, unknowns - f, Nil, Nil, Nil, rest, hard, rules_)
        val second =
          solve(solver, consts, funs, datatypes, unknowns, Nil, Nil, Nil, rest, hard, rules)

        first ++ second

      case (Nil, Nil, Nil, G(f, args, body) :: rest, hard) =>
        solve(solver, consts, funs, datatypes, unknowns, Nil, Nil, Nil, guess, hard, rules)

      case (Nil, Nil, Nil, Nil, (first @ B(xs, b, zs, lhs, rhs, guard)) :: rest) =>
        val Depth = 2
        val MaxVar = 1

        if (false) {
          val eqs =
            for ((expr, _) <- enumerate(funs, consts, b.res, Map(zs map (_ -> MaxVar): _*), Depth))
              yield {
                val eq = Rule(App(b, zs), expr)
                if (debug)
                  println("  trying: " + eq)
                val rules_ = rules + (b -> List(eq))
                // val lhs_ = Simplify.simplify(lhs, rules_, constrs)
                // val rhs_ = Simplify.simplify(rhs, rules_, constrs)
                (lhs, rhs, rules_)
              }

          for (
            (lhs, rhs, rules_) <- eqs;
            result <- solve(
              solver,
              consts,
              funs,
              datatypes,
              unknowns,
              Nil,
              Nil,
              List(A(lhs, rhs, guard)),
              Nil,
              rest,
              rules_
            )
          )
            yield result
        } else {
          val eq = Rule(lhs, rhs, guard)
          val eq_ = Simplify.simplify(eq, rules, Set())
          if (debug) {
            println("cannot solve hard query solve for: " + b)
            // rules map println
            println("  " + eq)
            println("  " + eq_ + " (simplified)")
          }

          for (
            (unknowns_, todo, rules) <- solve(
              solver,
              consts,
              funs,
              datatypes,
              unknowns,
              Nil,
              Nil,
              Nil,
              Nil,
              rest,
              rules
            )
          )
            yield (unknowns_, eq_ :: todo, rules)
        }
    }

  var neutral = {
    val int: Type = Sort.int // cast to Type
    val bool: Type = Sort.bool

    def make(op: Sugar.commutative) =
      (o: Fun, b: Fun, xs: List[Var]) => {
        val eq1 = Rule(b(), op.neutral)
        val eq2 = Rule(App(o, xs), op(xs))
        (eq1, eq2)
      }

    val known = Map(
      (List(int, int), int) -> LazyList(make(Plus), make(Times)),
      (List(bool, bool), bool) -> LazyList(make(Or), make(And))
    )

    known.withDefaultValue(LazyList.empty)
  }

  def select(fun: Fun, typ: Type) = {
    try {
      val inst = fun.generic
      val ty = Type.bind(inst.res, typ)
      LazyList((inst subst ty))
    } catch {
      case e: Type.CannotBind =>
        LazyList()
    }
  }

  def enumerate(
      funs: LazyList[Fun],
      consts: LazyList[Expr],
      types: List[Type],
      zs0: Map[Var, Int],
      depth: Int
  ): LazyList[(List[Expr], Map[Var, Int])] = types match {
    case Nil =>
      LazyList((Nil, zs0))

    case typ :: rest =>
      for (
        (expr, zs1) <- enumerate(funs, consts, typ, zs0, depth);
        (exprs, zs2) <- enumerate(funs, consts, rest, zs1, depth)
      )
        yield (expr :: exprs, zs2)
  }

  def enumerate(
      funs: LazyList[Fun],
      consts: LazyList[Expr],
      typ: Type,
      zs: Map[Var, Int],
      depth: Int
  ): LazyList[(Expr, Map[Var, Int])] = if (depth == 0) {
    LazyList()
  } else {
    val first =
      LazyList.from(
        for ((z, k) <- zs if z.typ == typ && k > 0)
          yield (z, zs + (z -> (k - 1)))
      )

    val second =
      for (c <- consts if c.typ == typ)
        yield (c, zs)

    val next =
      for (
        fun <- funs;
        inst <- select(fun, typ)
      )
        yield inst

    val third =
      for (
        inst <- next;
        (args, zs_) <- enumerate(funs, consts, inst.args, zs, depth - 1)
      )
        yield (App(inst, args), zs_)

    first ++ second ++ third
  }
}

object Foo {
  def main(args: Array[String]) {
    val st = State.default

    val zs =
      Map(
        Var("x", Sort.int) -> 1,
        Var("y", Sort.int) -> 1
      )

    val cs = LazyList(
      True,
      False,
      Zero,
      One
    )

    val results = Deaccumulate.enumerate(st.funs.values.to(LazyList), cs, Sort.int, zs, 3)

    for (result <- results)
      println(result)
  }
}

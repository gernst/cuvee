package cuvee.lemmas.deaccumulate

import cuvee.pure._
import cuvee.util.Name
import cuvee.smtlib.Model
import cuvee.smtlib.Solver
import cuvee.State
import cuvee.smtlib.Unsat
import cuvee.lemmas._

object Deaccumulate {
  // case object CannotDeaccumulate extends Exception
  var debug = false

  var heuristics = 0

  class Cond(val prio: Int)

  // Heuristic: look for neutral elements of o
  case class N(o: Fun, b: Fun) extends Cond(0)

  // Heuristic: define f(args) := body
  case class D(f: Fun, args: List[Var], body: Expr) extends Cond(1)

  // Assert g ==> l == r to validate some prior instantiation,
  // not generated as part of the original query, only during solving
  case class A(formals: List[Var], l: Expr, r: Expr, g: Expr) extends Cond(2)

  // Heuristic: guess f(args) := body, taken from existing function definition
  case class G(f: Fun, args: List[Var], body: Expr) extends Cond(3)

  // General case for function body b(args): find b so that forall formals. g ==> l == r
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
  ): (Def, Expr, Fun, List[Fun], List[Rule], List[Cond]) = {
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

          // skel is the abstracted body, where all recursive calls have been replaced by variables ys
          val (skel, recs) = abstracted(f, body)
          val (ys, arglists) = recs.unzip

          // list of static variables in this particular case
          val zs = static_ map args collect { case z: Var =>
            z
          }

          // assumptions needed for hoisting (one?) static base case
          val isBaseCase = recs.isEmpty
          val isStaticBody = ((body.free - u) subsetOf zs.toSet)

          // check whether it makes sense at all:
          // base cases that are not referring to the accumulator
          // can (probably) remain the same
          val refersToAccumulator = (u in body)

          if (isBaseCase && refersToAccumulator && isStaticBody) {
            // apply static hoisting to this base case:

            // prepare a placeholder for the definition of the body
            val n = Name("body", Some(j))
            val b = Fun(n, params, Nil, res)
            val body_ = b()
            val cs_ = C(args_, guard, body_)

            // prepare a binary operator ⊙ that may be used to body,
            // so that the solution is read off neutral elements of that operator
            val m = Name("odot", Some(j))
            val ⊙ = Fun(m, params, List(res, res), res)
            val y = Expr.fresh("y", res)
            val z = Expr.fresh("z", res)

            val eq1 = Rule(⊙(body_, z), z)
            val eq2 = Rule(App(⊕, List(y, u) ++ zs), ⊙(y, body))

            (cs_, List(b, ⊙), (List(eq1, eq2), List(N(⊙, b), D(⊕, List(y, u) ++ zs, ⊙(y, body)))))
          } else {
            // adjust argument lists of recursive calls
            val arglists_ =
              for ((y, args) <- recs)
                yield App(f_, args removed pos)

            val n = Name("phi", Some(j))
            val b = Fun(n, params, xs_.types ++ ys.types, res)
            val body_ = App(b, xs_ ++ arglists_)
            val cs_ = C(args_, guard, body_)

            // compute original body with recursive calls replaced
            // to new function and shorter argument lists
            val su_ = Expr.subst(ys, arglists_)
            val orig_ = skel subst su_

            // all variables possibly occurring in the constraints
            val vs = (u :: xs_ ++ ys ++ zs).distinct

            // substitution that replaces recursive calls by inductive hypothesis
            val acc =
              for ((y, args) <- recs)
                yield (y, App(⊕, List(y, args(pos)) ++ zs))

            val su = Expr.subst(acc)

            // this gives the lhs used in the actual proof obligation
            val lhs = skel subst su
            val rhs = App(⊕, List(App(b, xs_ ++ ys), u) ++ zs)
            val eq = Rule(rhs, lhs, And(guard))

            val accumulatorIsStatic = (static contains pos)

            // this condition holds, if the accumulator is not used somewhere else in the body,
            // which means it is just passed down at that same argument position
            val accumulatorDisappears = (orig_.free subsetOf args_.free)

            // TODO: document what happens here!
            val conds =
              if (recs.nonEmpty && accumulatorIsStatic && accumulatorDisappears) {
                // offer a guess here that the body will remain unchanged,
                // for a *recursive* case when that makes sense
                // - we have an accumulator that is actually unchanged passing it downwards, and
                // - we do not need the accumulator otherwise

                // perhaps this heuristic is not useful for reverse:0:append (XXX: this may not be accurate!)

                val guess = G(b, xs_ ++ ys, skel)
                val cond = B(vs, b, xs_ ++ ys, rhs, rhs, And(guard))
                List(guess, cond)
              } else if (recs.length == 1 && u.typ == res) { // direct accumulator
                // offer a guess when the accumulator actually does change but we have a single recursive call only,
                // the rationale for not trying this when there are multiple recursive calls is that then ⊕ must be idempotent or something like that
                // which seems unlikely to be satisfied

                // the guess is that we can just tail-recurse without considering the original body skel at all,
                // which only works if the type of the accumulator is what the function returns

                // TODO: document when that is useful!
                val List((y, args)) = recs
                val acc = args(pos) subst Map(u -> y)
                val guess = G(b, xs_ ++ ys, acc)
                val cond = B(vs, b, xs_ ++ ys, lhs, rhs, And(guard))
                List(guess, cond)
              } else {
                // otherwise, we have to work harder :)
                val cond = B(vs, b, xs_ ++ ys, lhs, rhs, And(guard))
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
        val cond = A(args, App(f, args), body, True)
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

      case (Nil, Nil, (cond @ A(xs, lhs, rhs, guard)) :: rest, _, _) =>
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

            val phi = Forall(xs, Imp(guard_, Eq(lhs_, rhs_)))
            if (debug)
              print("proving:  " + phi + " ... ")

            val s = lhs_ == rhs_
            val a = s || solver.isTrue(phi)
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
          List(A(xs, lhs, rhs, guard)),
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
          cuvee.error("add consts!")
          val eqs =
            for ((expr, _) <- enumerate(b.res, funs, Map(zs map (_ -> MaxVar): _*), Depth))
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
              List(A(xs, lhs, rhs, guard)),
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

  val defaultNeutral = {
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

  var neutral = defaultNeutral

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
      types: List[Type],
      funs: LazyList[Fun],
      base0: Map[Expr, Int],
      depth: Int
  ): LazyList[(List[Expr], Map[Expr, Int])] = types match {
    case Nil =>
      LazyList((Nil, base0))

    case typ :: rest =>
      for (
        (expr, base1) <- enumerate(typ, funs, base0, depth);
        (exprs, base2) <- enumerate(rest, funs, base1, depth)
      )
        yield (expr :: exprs, base2)
  }

  def enumerate(
      typ: Type,
      funs: LazyList[Fun],
      base: Map[Expr, Int],
      depth: Int
  ): LazyList[(Expr, Map[Expr, Int])] = if (depth == 0) {
    LazyList()
  } else {
    val first =
      LazyList.from(
        for ((z, k) <- base if z.typ == typ && k > 0)
          yield (z, base + (z -> (k - 1)))
      )

    val next =
      for (
        fun <- funs;
        inst <- select(fun, typ)
      )
        yield inst

    val second =
      for (
        inst <- next;
        (args, base_) <- enumerate(inst.args, funs, base, depth - 1)
      )
        yield (App(inst, args), base_)

    first ++ second
  }
}

object Foo {
  def main(args: Array[String]) {
    val st = State.default

    val zs =
      Map(
        (Var("x", Sort.int): Expr) -> 1,
        (Var("y", Sort.int): Expr) -> 1,
        True -> 1,
        False -> 1,
        Zero -> 1,
        One -> 1
      )

    val results = Deaccumulate.enumerate(Sort.int, st.funs.values.to(LazyList), zs, 3)

    for (result <- results)
      println(result)
  }
}

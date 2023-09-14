package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.smtlib._
import cuvee.util.Tool
import cuvee.util.Name
import cuvee.prove.InductiveProver
import cuvee.pipe.Stage
import cuvee.lemmas.prepare

object Lemmas extends Stage {
  val rounds = 3

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State) =
    if (cmds.nonEmpty && last == CheckSat) {
      val (decls, defs) = prepare(cmds, state)
      // val results = cuvee.lemmas.Test.run(decls, cmds, defs, state)

      implicit val solver = Solver.z3(100)
      Deaccumulate.neutral = Deaccumulate.defaultNeutral

      for (cmd <- cmds) cmd match {
        case SetLogic(_)      =>
        case _: Lemma         =>
        case Assert(Not(phi)) =>
        case _ =>
          solver.exec(cmd, null)
      }

      val goals =
        for ((Assert(Not(phi))) <- cmds)
          yield phi

      val lemmas = new Lemmas(decls, cmds, defs, state, solver)

      for (
        Lemma(phi, _, _) <- cmds;
        Rule(lhs, rhs, cond, Nil) <- Rules.from(phi, lemmas.original)
      ) {
        lemmas.addLemma("provided", lhs, rhs, cond)
        // lemmas.lemmas = ("provided", eq) :: lemmas.lemmas
      }

      lemmas.findNeutral(defs map (_.fun))

      for (df <- defs) {
        lemmas.define(df)
        lemmas.deaccumulate(df)
        lemmas.recognizeConditional(df)
      }

      for (df <- defs; dg <- defs) {
        lemmas.fuse(df, dg)
      }

      for (i <- 0 until rounds) {
        lemmas.round()
        lemmas.cleanup()
        lemmas.next()
      }

      val results = lemmas.lemmas

      solver.ack(Exit)
      solver.destroy()

      val known = state.funs.values.toSet
      val add =
        for ((origin, rule) <- results if (origin != "provided") && (rule.funs subsetOf known))
          yield Lemma(rule.toExpr, None, true)

      val (pre, post) = cmds partition {
        case Assert(Not(expr)) =>
          false
        case _ =>
          true
      }
      pre ++ add ++ post
    } else {
      cmds
    }
}

class Lemmas(decls: List[DeclareFun], cmds: List[Cmd], defs: List[Def], st: State, solver: Solver) {
  var useAdtInd = false
  var useInternal = true
  var printTiming = false // may be undesirable if counting duplicates
  AdtInd.cached = false

  var debug = true

  val constrs = st.constrs

  // these are the operations that may fail
  sealed trait Pending

  // request to fuse f:pos:g and generate lemma lhs == f:pos:g(xs patch (pos ys))
  case class FuseAt(lhs: Expr, df: Def, xs: List[Expr], dg: Def, ys: List[Expr], pos: Int)
      extends Pending {
    def key = df.fun.name
    override def toString = "fuse " + Fuse.fused(df.fun.name, dg.fun.name, pos)
  }

  // request to deaccumulate f at pos into f' and generate lemma lhs == e?(f'(xs removed pos), xs)
  case class DeaccumulateAt(lhs: Expr, df: Def, xs: List[Expr], pos: Int, again: Boolean)
      extends Pending {
    def key = df.fun.name
    override def toString = "deaccumulate " + Deaccumulate.deaccumulated(df.fun.name, pos)
  }

  // request to cleanup a definition, possibly removing arguments, or recognizing constant and identity functions
  // maintaining lhs == df'(args') for the cleaned up version
  case class Recognize(asLemma: Option[String], lhs: Expr, df: Def, args: List[Expr])
      extends Pending {
    require(!(original contains df.fun))
    def key = df.fun.name
    override def toString = "recognize " + df.fun.name
  }

  // case class RecognizeConditional(df: Def, lhs: Expr, recogArg: List[Expr])
  case class RecognizeConditional(df: Def) extends Pending {
    override def toString = "recognize conditional " + df.fun.name
  }

  var original: Set[Fun] = st.funs.values.toSet
  var deaccumulated: Set[(Fun, Int)] = Set()
  var fused: Set[(Fun, Fun, Int)] = Set()

  // current worklist
  var pending: List[Pending] = Nil

  // previous attempts that failed in the past
  var failed: List[Pending] = Nil

  var definitions: List[Def] = Nil

  var candidates: List[(String, Rule)] = Nil
  var lemmas: List[(String, Rule)] = Nil

  var replace: List[Rule] = Nil
  var recover: List[Rule] = Nil

  def normalize = {
    // collect all rewrite rules to make progress
    val rw1 = replace
    val rw2 = definitions flatMap (_.rules)
    val rw3 = lemmas collect {
      case (why, eq) if eq.funs subsetOf original =>
        eq
    }
    val rws = rw1 ++ rw2 ++ rw3
    rws.groupBy(_.fun)
  }

  def rules = {
    // collect all known rewrite rules, in this order of preference
    val rw1 = replace
    val rw2 = definitions flatMap (_.rules)
    val rw3 = lemmas map (_._2)
    val rw4 = recover
    var rws = rw1 ++ rw2 ++ rw3 ++ rw4
    // rws = rws filterNot { case Rule(lhs, rhs, cond, avoid) => lhs == rhs }
    rws.groupBy(_.fun)
  }

  def todo(add: Pending) {
    todo(List(add))
  }

  def todo(add: List[Pending]) {
    pending = pending ++ add
  }

  def retry(add: Pending) {
    retry(List(add))
  }

  def retry(add: List[Pending]) {
    failed = failed ++ add
  }

  def addLemma(origin: String, eq: Rule) {
    maybeAddNeutral(eq)
    // println("adding lemma: " + eq)
    lemmas = (origin, eq) :: lemmas
  }

  def addLemma(origin: String, lhs: Expr, rhs: Expr, cond: Expr = True) {
    addLemma(origin, Rule(lhs, rhs, cond))
  }

  def replaceBy(lhs: Expr, rhs: Expr) {
    val eq = Rule(lhs, rhs)
    println("replace by: " + eq)
    replace = eq :: replace
    val re = replace.groupBy(_.fun)

    recover = recover map { case Rule(lhs, rhs, cond, avoid) =>
      val lhs_ = Simplify.simplify(lhs, re, constrs)
      // println(lhs + " ~> " + lhs_)
      Rule(lhs_, rhs, cond, avoid)
    }

    lemmas = lemmas flatMap { case (origin, eq @ Rule(lhs, rhs, cond, avoid)) =>
      val rhs_ = catchRewritingDepthExceeded {
        Simplify.simplify(rhs, re, constrs)
      }

      if (lhs == rhs_) Nil
      else {
        val eq_ = Rule(lhs, rhs_, cond, avoid)
        // println("simplified lemma: " + eq + " to " + eq_)
        List((origin, eq_))
      }
    }
  }

  def recoverBy(lhs: Expr, rhs: Expr) {
    val eq = Rule(lhs, rhs)
    recover = eq :: recover
  }

  def define(df: Def) {
    for (dg <- definitions.find(_.fun == df.fun)) {
      println(df)
      println(dg)
    }

    require(definitions.forall(_.fun != df.fun), "definition already known for: " + df.fun)

    definitions = df :: definitions

    for (eq <- df.rules)
      maybeAddNeutral(eq)
  }

  def deaccumulate(df: Def) {
    val xs = Expr.vars("x", df.fun.args)
    todo {
      for (pos <- Deaccumulate.mayDeaccumulateAt(df))
        yield {
          val lhs = App(df.fun, xs)
          DeaccumulateAt(lhs, df, xs, pos, true)
        }
    }
  }

  def fuse(df: Def, dg: Def) {
    val xs = Expr.vars("x", df.fun.args)
    val ys = Expr.vars("y", dg.fun.args)

    todo {
      for (pos <- Fuse.mayFuseAt(df, dg))
        yield {
          val lhs = App(df.fun, xs updated (pos, App(dg.fun, ys)))
          FuseAt(lhs, df, xs, dg, ys, pos)
        }
    }
  }

  def recognizeConditional(df: Def) {
    todo {
      RecognizeConditional(df)
    }
  }

  def drop(df: Def) {
    definitions = definitions filterNot (_ == df)
    require(
      definitions forall (_.fun != df.fun),
      "mismatching/unknown definition for function: " + df.fun
    )
  }

  def cleanup() {
    val rw1 = rules

    lemmas =
      for ((origin, eq @ Rule(lhs, rhs, cond, avoid)) <- lemmas)
        yield catchRewritingDepthExceeded {
          val rhs_ = Simplify.simplify(rhs, rw1, constrs)
          val cond_ = Simplify.simplify(cond, rw1, constrs)
          val eq_ = Rule(lhs, rhs_, cond_, avoid)
          // println("simplified lemma: " + eq + " to " + eq_)
          (origin, eq_)
        }

    lemmas = lemmas.distinct filterNot {
      _._2.cond == False
    }

    val rw2 = lemmas.map(_._2).groupBy(_.fun)

    definitions =
      for (df <- definitions)
        yield catchRewritingDepthExceeded {
          df.simplify(rw2, constrs)
        }
  }

  def next() {
    pending = failed
    failed = Nil
  }

  def show() {
    catchRewritingDepthExceeded {
      println()

      println("definitions:")
      for (df <- definitions; eq <- df.rules)
        println("  " + eq)
      println()

      // println("rules:")
      // for ((_, eqs) <- rules; eq <- eqs)
      //   println("  " + eq)
      // println()

      println("lemmas:")
      for ((origin, eq) <- lemmas) {
        println("  " + eq + " (" + origin + ")")
      }
      println()

      // println("retry:")
      // for (pending <- failed)
      //   println("  " + pending)
      // println()
    }
  }

  def round() {
    while (pending.nonEmpty) {
      val first = pending.head
      pending = pending.tail

      first match {
        case FuseAt(lhs, df, xs, dg, ys, pos) if !(fused contains ((df.fun, dg.fun, pos))) =>
          Fuse.fuseAt(df, xs, dg, ys, pos, st.constrs, normalize) match {
            case None =>
              if (debug)
                println("fuse " + lhs + " failed")
              retry(first)

            case Some((dfg, zs)) =>
              fused += ((df.fun, dg.fun, pos))
              val rhs = App(dfg.fun, zs)
              recoverBy(rhs, lhs)
              if (debug)
                println("fuse " + lhs + " == " + rhs)
              // println(dfg)
              todo { Recognize(Some("fused"), lhs, dfg, zs) }
            // todo {RecognizeConditional(dfg)}
          }

        case DeaccumulateAt(lhs, df, xs, pos, again) if !(deaccumulated contains ((df.fun, pos))) =>
          val (df_, rhs, oplus, unknowns, eqs, conds) =
            Deaccumulate.deaccumulateAt(df, xs, pos, df.staticArgs)

          val consts = LazyList[Expr]()
          // val consts = LazyList(Zero, One, True, False)

          // val funs0 = LazyList[Fun]()
          // val funs0 = LazyList(Fun.eq_, Fun.plus, Fun.minus, Fun.times, Fun.uminus, Fun.and, Fun.or)

          val funs0 = st.constrs.to(LazyList)

          val x = definitions filter (original contains _.fun) map (_.fun)
          val funs1 = x.to(LazyList)

          val funs = funs0 ++ funs1

          if (false) {
            println("goal: " + lhs + " == " + rhs)
            println("constants for deaccumulation synthesis")
            for (cst <- consts)
              println("  " + cst)
            println("extra functions for deaccumulation synthesis")
            for (fun <- funs0)
              println("  " + fun)
            println("original for deaccumulation synthesis")
            for (fun <- funs1)
              println("  " + fun)
            println("solving")
            for (eq <- eqs)
              println(eq)
            println("conds")
            for (eq <- conds)
              println(eq)

          }

          var solved = false

          if (!solved && useInternal) {
            catchRewritingDepthExceeded {
              // println("trying to solve query for: " + df_.fun)

              val solutions =
                Deaccumulate.solve(
                  solver,
                  consts,
                  funs,
                  st.datatypes,
                  unknowns.toSet,
                  conds,
                  normalize
                )
              // println("done")

              var iterator = Option(solutions)
              var counter = 0

              // for ((funs, rest, rules_) <- solutions) {
              while (iterator.nonEmpty) {
                val Some(solutions) = iterator

                val (ms, stuff) = Tool.time {
                  solutions.headOption
                }

                stuff match {
                  case None =>
                    iterator = None

                  case Some((funs, rest, rules_)) =>
                    iterator = Some(solutions.tail)
                    counter += 1

                    if (rest.isEmpty) {
                      val model = rules_.filter(unknowns contains _._1)
                      // println("model: ")
                      // for((_, eqs) <- model; eq <- eqs)
                      //   println(eq)
                      val df__ = df_ simplify (model, constrs)
                      val f__ = df__.fun
                      val n = f__.name.name

                      def xxx(name: Name) = name match {
                        case Name(`n`, None) =>
                          Name(n, Some(counter))
                        case _ =>
                          name
                      }
                      // make sure we have unique function names for the deaccumulated function if there are more than one solution
                      val f__i = f__ rename xxx

                      // println("rename " + f__ + " to " + f__i)

                      val df__i = df__ rename xxx

                      // println("simplified definition: " + df__)
                      val rhs_ = Simplify.simplify(rhs, model, constrs) replace (f__, f__i)
                      if (debug)
                        print(
                          "deaccumulate " + df.fun.name + xs
                            .updated(pos, "_")
                            .mkString("(", ", ", ")")
                        )
                      if (debug)
                        println(" == " + rhs_)
                      // println("  model: " + model)
                      // println("success: " + first)
                      if (printTiming)
                        addLemma("internal (" + ms + "ms)", lhs, rhs_)
                      else
                        addLemma("internal", lhs, rhs_)
                      // println("added lemma")
                      solved = true

                      // trigger further processing of synthetic function df__ independently
                      val ys = Expr.vars("x", f__i.args)
                      todo { Recognize(None, App(f__i, ys), df__i, ys) }
                      // todo {RecognizeConditional(df__i)}
                    }
                }
              }
            }
          }

          if (!solved && useAdtInd) {
            AdtInd.toQuery(oplus, unknowns.toSet, conds, st, normalize) match {
              case None =>
                println("translating problem into AdtInd currently not implemented")

              case Some((q, recover)) =>
                // println("trying AdtInd")

                val eq = Rule(lhs, rhs)

                val (ms, stuff) = Tool.time {
                  AdtInd.query(
                    q,
                    df,
                    df_,
                    eq,
                    decls,
                    cmds,
                    definitions filter (original contains _.fun),
                    st
                  )
                }

                println("AdtInd produced the following solutions:")
                for ((rules, k) <- stuff.zipWithIndex) {
                  // println("  solution " + k)
                  // for (eq <- rules)
                  //   println("   " + eq)
                  println()

                  val model = (recover ++ rules).groupBy(_.fun)
                  val df__ = df_ simplify (model, constrs)
                  // println("simplified definition: " + df__)
                  val rhs_ = Simplify.simplify(rhs, model, constrs)
                  print(
                    "deaccumulate " + df.fun.name + xs.updated(pos, "_").mkString("(", ", ", ")")
                  )
                  println(" == " + rhs_)
                  // println("success: " + first)
                  addLemma("AdtInd", lhs, rhs_)
                  // println("added lemma")
                  solved = true

                  // trigger further processing of synthetic function df__ independently
                  val ys = Expr.vars("x", df__.fun.args)
                  todo { Recognize(None, App(df__.fun, ys), df__, ys) }
                }
            }
          }

          if (!solved) {
            if (debug)
              print(
                "deaccumulate " + df.fun.name + xs.updated(pos, "_").mkString("(", ", ", ")")
              )
            if (debug)
              println("  failed")
            // for (fun <- unknowns)
            //   println("  " + fun)
            // for (eq <- eqs)
            //   println("  " + eq)
            // println()
            if (again)
              retry(first)
          }

        case Recognize(asLemma, lhs, df, args) =>
          // println("given definition")
          // println(df)
          if (debug)
            print("recognize " + lhs)

          val (changed, df_, args_) = catchRewritingDepthExceeded {
            Clenaup.cleanup(df simplify (normalize, constrs), args)
          }

          // todo {RecognizeConditional(df_)}

          val rhs1 = Trivial.constant(df_, args_) map ((_, "constant"))
          val rhs2 = Trivial.identity(df_, args_) map ((_, "identity"))
          val rhs3 = Trivial.selectsConstructors(df_, args_) map ((_, "constructors"))

          // note we assume that definitions get simplified in the mean time
          // between rounds, to make use of new lemmas found

          val rhs4 =
            for (
              dg <- definitions;
              _ = { if (debug) println("  trying: " + dg.fun.name) };
              (ty, perm) <- Known.known(df_, dg)
            ) yield {
              val rhs = App(Inst(dg.fun, ty), perm map args_)
              assert(!(original contains df.fun))
              drop(df_)
              (rhs, "as " + dg.fun)
            }

          val all = rhs1 ++ rhs2 ++ rhs3 ++ rhs4

          for ((rhs, why) <- all) {
            if (debug)
              println(" == " + rhs + " (" + why + ")")

            replaceBy(lhs, rhs)

            for (origin <- asLemma)
              addLemma(origin, lhs, rhs)
          }

          if (all.isEmpty) {
            if (definitions exists (_.fun == df_.fun)) {
              // note this definition may have been simplified
              if (debug)
                println(" exists")
            } else {
              if (debug)
                println(" new")
              // to be able to recognize duplicate synthetic functions
              define(df_)

              retry {
                // perhaps we can recognize this definition in the future,
                // when we have some more lemmas?
                Recognize(asLemma, lhs, df_, args_)
              }

              todo {
                RecognizeConditional(df_)
              }

              todo {
                // try deaccumulating but don't chain this query, it depends on the one above
                for (pos <- Deaccumulate.mayDeaccumulateAt(df_))
                  yield DeaccumulateAt(lhs, df_, args_, pos, again = true)
              }
            }
          }

        // case RecognizeConditional(df, lhs, recogArg) =>
        case RecognizeConditional(df) =>
          val Def(fun, cases) = df
          if (debug)
            println("recognize conditionally " + fun.name)

          val ids = Conditional.checkIdentityWithParamPicksAndGuard(df)
          val const = Conditional.checkIsDefConstant(df)

          val all = ids ++ const

          for ((rule, preCondDef) <- all) {
            addLemma("conditional identity", rule)
            val pre = preCondDef.fun
            val xs = Expr.vars("x", pre.args)
            val lhs = App(pre, xs)
            todo { Recognize(None, lhs, preCondDef, xs) }
          }

          // val other =
          //   for (
          //     dg <- definitions if (original contains dg.fun) && (df.fun != dg.fun) && (df.typ == dg.typ);
          //     (dpre, expr) <- cuvee.newlemmas.Compare.compare(df, dg, st.constrs)
          //   ) {
          //     println("HAVE: " + expr)
          //     println(dpre)
          //   }

        case _ =>
          if (debug)
            println("skipping: " + first)
      }
    }
  }

  def findNeutral(funs: Iterable[Fun]) {
    for (f <- funs) (f.args, f.res) match {
      case (List(left, right), res @ Sort(Con(name, _), _)) if st.datatypes contains name =>
        val dt = st datatypes name

        def holds(phi: Expr, x: Var) = x.typ match {
          case Sort(Con(name, _), _) if st.datatypes contains name =>
            val dt = st datatypes name
            val ind = InductiveProver.induction(phi, x, dt)
            var a = solver.isTrue(phi)
            val b = solver.isTrue(ind)
            if (!a && b) {
              val Forall(xs, Eq(lhs, rhs)) = phi
              addLemma("neutral", lhs, rhs)
            }
            val ok = a || b
            // println("trying " + phi + " with induction: " + ok)
            ok

          case _ =>
            val ok = solver.isTrue(phi)
            // println("trying " + phi + ": " + ok)
            ok
        }

        val base =
          for ((c, Nil) <- dt.constrs)
            yield App(c, res)

        if (left == res && right == res) {
          val x = Var("x", right)

          for (c <- base) {
            val lhs = App(f, List(c, x))
            val rhs = x
            val eq = Forall(List(x), Eq(lhs, rhs))

            if (holds(eq, x)) {
              maybeAddNeutral(Rule(lhs, rhs))
            }
          }
        }

        if (left == res && right == res) {
          val x = Var("x", left)

          for (c <- base) {
            val lhs = App(f, List(x, c))
            val rhs = x
            val eq = Forall(List(x), Eq(lhs, rhs))

            if (holds(eq, x)) {
              maybeAddNeutral(Rule(lhs, rhs))
            }
          }
        }

      case _ =>
    }
  }

  var leftNeutrals: Set[(Fun, Expr)] = Set()
  var rightNeutrals: Set[(Fun, Expr)] = Set()

  def maybeAddNeutral(eq: Rule) {
    import Deaccumulate.neutral

    eq match {
      // don't add neutral laws for synthetic functions,
      // this unfortunately can lead to rewriting loops (example append:0:reverse)
      case Rule(App(f, List(e, y: Var)), z, True, _)
          if (original contains f.fun) && y == z && e.free.isEmpty =>
        val rule =
          (o: Fun, b: Fun, xs: List[Var]) => {
            val eq1 = Rule(b(), e)
            val eq2 = Rule(App(o, xs), App(f, xs))
            (eq1, eq2)
          }

        if (!(leftNeutrals contains (f.fun, e))) {
          if (debug)
            println("left-neutral: " + eq)
          leftNeutrals += ((f.fun, e))
          val key = (f.args, f.res)
          val old = neutral(key)
          neutral += key -> old.prepended(rule)
        }

      case Rule(App(f, List(x: Var, e)), z, True, _)
          if (original contains f.fun) && x == z && e.free.isEmpty =>
        val rule =
          (o: Fun, b: Fun, xs: List[Var]) => {
            val eq1 = Rule(b(), e)
            val eq2 = Rule(App(o, xs), App(f, xs.reverse))
            (eq1, eq2)
          }

        if (!(rightNeutrals contains (f.fun, e))) {
          if (debug)
            println("right-neutral: " + eq)
          rightNeutrals += ((f.fun, e))
          val key = (f.args.reverse, f.res)
          val old = neutral(key)
          neutral += key -> old.prepended(rule)
        }

      case _ =>
      // println("  not a neutral rule: " + eq)
    }
  }

  def catchRewritingDepthExceeded[A](f: => A) = {
    try {
      f
    } catch {
      case e @ Rewrite.RewriteDepthExceeded(trace, rules) =>
        println("rewriting depth exceeded")
        println()

        println("trace:")
        for (expr <- trace)
          println("  " + expr)
        println()
        println("rewrite rules:")
        for ((fun, eqs) <- rules) {
          println("  " + fun)
          for (eq <- eqs)
            println("    " + eq)
        }
        println()

        println("replace:")
        for (eq <- replace)
          println("  " + eq)
        println("definitions:")
        for (eq <- definitions flatMap (_.rules))
          println("  " + eq)
        println("lemmas:")
        for (eq <- lemmas map (_._2))
          println("  " + eq)
        println("recover:")
        for (eq <- recover)
          println("  " + eq)

        e.printStackTrace()

        throw e
    }
  }
}

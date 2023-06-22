package cuvee.lemmas

import cuvee.pure._
import cuvee.State
import cuvee.smtlib._
import cuvee.util.Tool
import cuvee.util.Name
import cuvee.prove.InductiveProver

class Lemmas(decls: List[DeclareFun], cmds: List[Cmd], defs: List[Def], st: State, solver: Solver) {
  var useAdtInd = false
  var useInternal = true
  var printTiming = false // may be undesirable if counting duplicates
  AdtInd.cached = false

  val constrs = st.constrs

  // these are the operations that may fail
  sealed trait Pending {
    def key: Name
  }

  implicit class PendingList(ps: List[Pending]) {
    def keys = ps map (_.key)
  }

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

  def addLemma(origin: String, lhs: Expr, rhs: Expr, cond: Expr = True) {
    val eq = Rule(lhs, rhs, cond)
    maybeAddNeutral(eq)
    // println("adding lemma: " + eq)
    lemmas = (origin, eq) :: lemmas
  }

  def replaceBy(lhs: Expr, rhs: Expr) {
    val eq = Rule(lhs, rhs)
    replace = eq :: replace

    lemmas = lemmas flatMap { case (origin, eq @ Rule(lhs, rhs, cond, avoid)) =>
      val rhs_ = catchRewritingDepthExceeded {
        Simplify.simplify(rhs, replace.groupBy(_.fun), constrs)
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

    lemmas = lemmas.distinct

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
              println("fuse " + lhs + " failed")
              retry(first)

            case Some((dfg, zs)) =>
              fused += ((df.fun, dg.fun, pos))
              val rhs = App(dfg.fun, zs)
              recoverBy(rhs, lhs)
              println("fuse " + lhs + " == " + rhs)
              todo { Recognize(Some("fused"), lhs, dfg, zs) }
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
                      print(
                        "deaccumulate " + df.fun.name + xs
                          .updated(pos, "_")
                          .mkString("(", ", ", ")")
                      )
                      println(" == " + rhs_)
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
            print(
              "deaccumulate " + df.fun.name + xs.updated(pos, "_").mkString("(", ", ", ")")
            )
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
          print("recognize " + lhs)

          val (changed, df_, args_) = catchRewritingDepthExceeded {
            Unused.unused(df simplify (normalize, constrs), args)
          }

          val rhs1 = Trivial.constant(df_, args_) map ((_, "constant"))
          val rhs2 = Trivial.identity(df_, args_) map ((_, "identity"))

          // note we assume that definitions get simplified in the mean time
          // between rounds, to make use of new lemmas found
          val rhs3 = for ((dg, ty, perm) <- Known.known(df_, definitions)) yield {
            val rhs = App(Inst(dg.fun, ty), perm map args_)
            assert(!(original contains df.fun))
            drop(df_)
            (rhs, "as " + dg.fun)
          }

          val all = rhs1 ++ rhs2 ++ rhs3

          for ((rhs, why) <- all) {
            println(" == " + rhs + " (" + why + ")")

            replaceBy(lhs, rhs)

            for (origin <- asLemma)
              addLemma(origin, lhs, rhs)
          }

          if (all.isEmpty) {
            if (definitions exists (_.fun == df_.fun)) {
              // note this definition may have been simplified
              println(" exists")
            } else {
              println(" new")
              // to be able to recognize duplicate synthetic functions
              define(df_)

              retry {
                // perhaps we can recognize this definition in the future,
                // when we have some more lemmas?
                Recognize(asLemma, lhs, df_, args_)
              }

              todo {
                // try deaccumulating but don't chain this query, it depends on the one above
                for (pos <- Deaccumulate.mayDeaccumulateAt(df_))
                  yield DeaccumulateAt(lhs, df_, args_, pos, again = true)
              }
            }
          }

        case _ =>
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
            if(!a && b) {
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

        println("left-neutral: " + eq)
        val key = (f.args, f.res)
        val old = neutral(key)
        neutral += key -> old.prepended(rule)

      case Rule(App(f, List(x: Var, e)), z, True, _)
          if (original contains f.fun) && x == z && e.free.isEmpty =>
        val rule =
          (o: Fun, b: Fun, xs: List[Var]) => {
            val eq1 = Rule(b(), e)
            val eq2 = Rule(App(o, xs), App(f, xs.reverse))
            (eq1, eq2)
          }

        println("right-neutral: " + eq)
        val key = (f.args.reverse, f.res)
        val old = neutral(key)
        neutral += key -> old.prepended(rule)

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

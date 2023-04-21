package cuvee.lemmas

import cuvee.StringOps
import cuvee.backtrack
import cuvee.toControl
import cuvee.pure._
import cuvee.State
import cuvee.util.Name
import cuvee.smtlib._
import cuvee.util.Tool
import java.io.File
import scala.io.Source
import java.io.StringReader

case class Query(b: Fun, oplus: Fun, rest: List[Fun], base: Expr, conds: List[Expr]) {
  def typ = b.res
  def constraints = base :: conds
  def funs = b :: oplus :: rest

  override def toString = {
    funs.mkString("exists\n  ", "\n  ", "\n") + constraints.mkString(
      "where\n  ",
      "\n  ",
      ""
    )
  }

  def cmds = {
    val decls =
      for (Fun(name, Nil, args, res) <- funs)
        yield DeclareFun(name, args, res)

    val conds =
      for (phi <- constraints)
        yield Assert(phi)

    decls ++ conds
  }

}

object AdtInd {
  var cached = false
  var promoteAll = true

  /*
(assert (= $0 0))
(assert (= $1 1))
(assert (= $false false))
(assert (= $true true))
   */

  val predefined = List(
    "(declare-fun $0 () Int)",
    "(declare-fun $1 () Int)",
    "(declare-fun $true () Bool)",
    "(declare-fun $false () Bool)",
    "(assert (forall ((x Int)) (= $0 0)))",
    "(assert (forall ((x Int)) (= $1 1)))",
    "(assert (forall ((x Int)) (= $false false)))",
    "(assert (forall ((x Int)) (= $true true)))",
    "(declare-fun $+   (Int Int) Int)",
    "(declare-fun $*   (Int Int) Int)",
    "(declare-fun $or  (Bool Bool) Bool)",
    "(declare-fun $and (Bool Bool) Bool)",
    "(assert (forall ((x Int) (y Int))   (= ($+ x y)   (+ x y))))",
    "(assert (forall ((x Int) (y Int))   (= ($* x y)   (* x y))))",
    "(assert (forall ((x Bool) (y Bool)) (= ($or x y)  (or x y))))",
    "(assert (forall ((x Bool) (y Bool)) (= ($and x y) (and x y))))"
    // "(declare-fun $eq   (Elem Elem) Bool)",
    // "(assert (forall ((x Elem) (y Elem)) (= ($eq x y) (= x y))))"
  )

  val renaming = Map(
    "$0" -> cuvee.sexpr.Lit.num("0"),
    "$1" -> cuvee.sexpr.Lit.num("1"),
    "$true" -> cuvee.sexpr.Id("true"),
    "$false" -> cuvee.sexpr.Id("false"),
    "$+" -> cuvee.sexpr.Id("+"),
    "$*" -> cuvee.sexpr.Id("*"),
    "$or" -> cuvee.sexpr.Id("or"),
    "$and" -> cuvee.sexpr.Id("and")
    // "$eq" -> cuvee.sexpr.Id("=")
  )

  def query_(
      q: Query,
      df: Def,
      df_ : Def,
      eq: Rule,
      decls: List[DeclareFun],
      cmds: List[Cmd],
      defs: List[Def],
      st0: State
  ): List[List[Rule]] = {
    println(eq)
    println(q)
    val Query(b, oplus, rest, base, conds) = q
    println()
    Nil
  }

  def toQuery(
      oplus_! : Fun,
      unknowns: Set[Fun],
      all: List[Deaccumulate.Cond],
      known: Map[Fun, List[Rule]]
  ): Option[(Query, List[Rule])] = {
    import Deaccumulate._

    val neutrals = all collect { case c: N => c }
    val easy = all collect { case c: A => c }
    assert(easy.isEmpty, "all easy cases should be presented as guesses instead")

    neutrals match {
      case Nil =>
        val hard = all collect { case c: B => c }
        require(hard.nonEmpty, "empty deaccumulation query: " + all)

        val (base, rec) = hard partition {
          case B(body, xs, App(`oplus_!`, App(body_, ys) :: args), r, g) if body == body_.fun =>
            true
          case _ =>
            false
        }

        base match {
          case List(B(body, xs, App(_, App(_, ys) :: args), r, g)) =>
            val b = body rename (_ => "b")
            val oplus = oplus_! rename (_ => "oplus")

            None
          case _ =>
            None
        }

      case List(N(odot, body)) =>
        val b = body rename (_ => "b")
        val oplus = odot rename (_ => "oplus")

        val defs = for (D(f, xs, App(Inst(odot_, _), args @ List(z, arg))) <- all) yield {
          assert(odot == odot_)
          (arg, Rule(App(f, xs), App(oplus, args)))
        }

        val (args, rules) = defs.unzip

        val xs = Expr.vars("x", b.args)
        val ys = Expr.vars("y", oplus.args)

        val recover = rules ++ List(
          Rule(App(body, xs), App(b, xs)),
          Rule(App(odot, ys), App(oplus, ys))
        )

        val as = Expr.vars("a", args.types)

        val abs = (args zip as).toMap

        val rw = known ++ rules.groupBy(_.fun)

        val hard = for (B(b, args, lhs, rhs, guard) <- all) yield {
          val lhs_ = Simplify.simplify(lhs, rw) topdown {
            case expr if abs contains expr =>
              abs(expr)
            case expr =>
              expr
          }

          val rhs_ = Simplify.simplify(rhs, rw) topdown {
            case expr if abs contains expr =>
              abs(expr)
            case expr =>
              expr
          }

          val guard_ = Simplify.simplify(guard, rw)
          (b, Clause(args ++ as, guard_, Eq(rhs_, lhs_)))
        }

        val (rest, conds) = hard.unzip

        val z = Var("z", oplus.args(0))
        val base = Forall(List(z), Eq(z, oplus(b(), z)))

        val q = Query(b, oplus, rest, base, conds)
        // println(q)
        Some((q, recover))

      case _ =>
        None
    }
  }

  def query(
      q: Query,
      df: Def,
      df_ : Def,
      eq: Rule,
      decls: List[DeclareFun],
      cmds: List[Cmd],
      defs: List[Def],
      st0: State
  ): List[List[Rule]] = {
    val dir = "queries/"
    new File(dir).mkdirs()

    val file = dir + df_.fun.name + ".smt2"
    val tmp = log(file)

    val m = predefined.count { line =>
      line.startsWith(("(assert"))
    }

    // don't reuse the function we are rewriting
    val axioms =
      for (
        df <- defs if df.fun != eq.fun;
        cmd <- df.axioms
      )
        yield cmd

    val n = axioms.count {
      case _: Assert => true
      case _         => false
    }

    // synthetic equality predicates for non-generic types
    // TODO: later add all monomorphic instances e.g. for List
    val eqs_and_renaming = for (Con(name, 0) <- st0.cons.values.toList) yield {
      val sort = st0.sort(name)
      val x = Var("x", sort)
      val y = Var("y", sort)
      val n = "$eq_" + name
      val n_ = Name(n)
      // println(n_)
      val f = Fun(n_, Nil, List(sort, sort), Sort.bool)
      val decl = DeclareFun(n_, List(sort, sort), Sort.bool)
      val defn = Assert(Forall(List(x, y), Eq(App(f, List(x, y)), Eq(x, y))))
      (decl, defn) -> (n, cuvee.sexpr.Id("="))
    }

    val (eqs, eqre) = eqs_and_renaming.unzip
    val k = eqs.length

    val skip = m + n + k
    val ind = Array("./ind", "--defs", skip.toString, file)
    val cat = Array("cat", file + ".out")

    // document how to run this file
    tmp println ind.mkString("; ", " ", "")
    tmp.println

    for (cmd @ DeclareSort(_, _) <- cmds) {
      dump(tmp, cmd)
    }

    for (cmd @ DeclareDatatypes(_, _) <- cmds) {
      dump(tmp, cmd)
    }

    // val decls =
    //   for (df <- defs)
    //     yield df.decl

    for (cmd <- decls)
      dump(tmp, cmd)

    val x = Var("x", Sort.int)

    // for (cmd <- axioms)
    //   dump(tmp, cmd)

    for (cmd <- axioms) {
      cmd match {
        case Assert(_ @Forall(_, _)) =>
          dump(tmp, cmd)

        case Assert(phi) =>
          val cmd_ = Assert(Bind(Quant.forall, List(x), phi, Sort.bool))
          tmp println ("; dummy quantifier")
          dump(tmp, cmd_)

        case _ =>
          dump(tmp, cmd)
      }
    }

    tmp.println("; predefined abbreviations")
    for (cmd <- predefined)
      tmp.println(cmd)
    tmp.println()

    tmp.println("; synthetic equality predicates")
    for ((decl, defn) <- eqs) {
      dump(tmp, decl)
      dump(tmp, defn)
    }
    tmp.println()

    tmp.println("; original definition")
    tmp.println()

    for (cmd <- df.cmds)
      dump(tmp, cmd, true)

    tmp.println("; promoted definition")
    tmp.println()

    for (cmd <- df_.cmds)
      dump(tmp, cmd, true)

    tmp.println("; query for " + df_.fun.name)
    tmp.println()

    for (cmd <- q.cmds)
      dump(tmp, cmd)
    tmp.println()

    tmp.println("; lemma ")
    dump(tmp, eq, true)

    tmp.close()

    var timeout = 60_000
    var allSolutions = false

    var solutions: List[List[Rule]] = Nil

    if (timeout > 0) {
      val args = if (cached) cat else ind
      val dump = if (cached) NO else log(file + ".out")

      val (in, out, err, proc) =
        Tool.pipe(args: _*)

      def kill() {
        // println("killed")
        proc.destroyForcibly()
      }

      Tool.withTimeout(timeout, kill()) {
        var line = out.readLine()
        var done = false

        while (line != null && !done) {
          dump.println(line)

          while (line != null && line != "model:" && line != "done") {
            // if (line startsWith "replacing")
            //   println(line)
            line = out.readLine()
            // println(line)
            dump.println(line)
          }
          // println()

          if (line == "model:") {
            // println("solved")
            line = out.readLine()
            // println(line)
            dump.println(line)

            var text = new StringBuilder
            while (line != null && line.trim.nonEmpty) {
              text append line
              line = out.readLine()
              // println(line)
              dump.println(line)
            }

            val st1 = st0.copy()
            val text_ = text.toString
            val reader = new StringReader(text_)
            val from = cuvee.trace("scanning:\n" + text_) {
              cuvee.sexpr.parse(reader)
            }

            val re = renaming ++ eqre
            val from_ = from map (_ replace re)
            val res = cuvee.trace("parsing:\n" + from_) {
              cuvee.smtlib.parse(from_, st1)
            }

            val eqs =
              for (DefineFun(name, xs, res, rhs, false) <- res)
                yield {
                  val fun = st1 funs (name, xs.length)
                  val lhs = App(fun, xs)
                  val eq = Rule(lhs, rhs)
                  println(eq)
                  eq
                }
            println()

            solutions = eqs :: solutions

            if (!allSolutions)
              done = true
          }

          if (line == "done" || done) {
            // println("acknowledging")
            in.println()
            in.flush()
            line = null
            kill()
          }
        }
      }
    }

    solutions
  }
}

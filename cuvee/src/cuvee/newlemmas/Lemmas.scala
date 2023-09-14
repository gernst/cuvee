package cuvee.newlemmas

import cuvee.State
import cuvee.pure._

class Lemmas(init: List[Def], state: State) {
  self =>

  trait Pending {
    def context = self
  }

// implementation of the transformers corresponding to pending todos,
// returns a list of potential successes, each with
// - generated normalization rules
// - generated lemma candidates
// - new synthetic definitions
  trait Transform[A <: Pending] {
    def apply(pending: A): List[(List[Rule], List[Expr], List[Def])]
  }

  val constrs = state.constrs

  var defs: List[Def] = init
  val original = Set(defs map (_.fun): _*)

  // keep track of synthetic functions up to MaxLevel,
  // where level 0 is original
  val level = Map(defs map (_.fun -> 0): _*)
  val MaxLevel = 2

  // TODO: fusion with conditional rewrites??
  // TODO: deaccumulate non-accumulators?
  // TODO: specialize, e.g. drop where length smaller than and sub?

  // lemma?:  lemma candidates that need to be recovered to original functions
  // norm:    use eagerly during normalization
  // drop!:   remove *now* function on the lhs from the list of definitions
  // recover: use when going back to original theory functions
  // unsafe:  potentially unsafe rule, add to norm later

  var lemmas_? : List[Expr] = Nil
  var lemmas: Set[Expr] = Set()

  var unsafe: List[Rule] = Nil
  var normalize: List[Rule] = Nil

  var recover: List[Rule] = Nil

  // request to look at f(xs) and generate potential lemmas
  //   f(xs) = c(us)   [norm,lemma?]     if the function is constant in static arguments us
  //   f(xs) = xs_i    [norm,lemma?]     if the function is the identity in the ith argument
  //   f(xs) = f'(xs') [norm,drop]       after removing some arguments of synthetic, warn if f is original
  // otherwise, try to recover f in terms of known function g
  //   f(xs) = g(xs')  [norm,drop!]       if synthetic f is structurally identical to g
  // then, infer conditional lemmas
  //   pre(xs) ==> f(xs) = c(us)     [lemma?]
  //   pre(xs) ==> f(xs) = xs_i      [lemma?]
  //   pre(xs,ys) ==> f(xs) = g(ys)  [lemma?]
  // also apply special processing for boolean functions, e.g. case splits, hoisting, equations to substitution
  //   p(xs) <== p'(xs') /\ q(us) [weaken]     for static us, because we do not know whether q is actually triggered during traversal, but we can for sure say *one* of the base cases is triggered!
  //   p(xs) ==> x_i = e(us)      [strengthen] unclear (?), may rely on absence of underspecification
  case class Process(df: Def) extends Pending

  // request to fuse f:pos:g and generate lemma
  // f(xs patch (pos -> g(ys))) == f:pos:g(xs patch (pos -> ys)) [lemma?,norm,recover]
  case class FuseAt(df: Def, dg: Def, pos: Int) extends Pending

  // request to deaccumulate f at pos into f' and generate
  // f(xs) == e?(f'(xs removed pos), xs) [lemma?,unsafe]
  case class DeaccumulateAt(df: Def, pos: Int) extends Pending

  // what to do in this round
  var pending: List[Pending] = Nil

  // what failed and can be retried next round
  var failed: List[Pending] = Nil

  def todo(add: Pending) { todo(List(add)) }
  def todo(add: List[Pending]) { pending = pending ++ add }
  def retry(add: Pending) { retry(List(add)) }
  def retry(add: List[Pending]) { failed = failed ++ add }

  // overall pipeline: a definition enters into this algorithm and will be
  // 1. cleaned up (remove unused arguments, normalized via known rules)
  // 2. recognized (identity, constant, other function)
  // 3. used to generate conditional identities
  // 4. deaccumulated at any potential arguments/base cases
  // 5. fused with any other definition, up to a certain level overall

  // 1. and 2. need to be done first always

  // conditional lemmas, deaccumulation, and fusion are independent of each other,
  // fusion considers only *recursive* arguments, wheras deaccumulation considers only *accumulators*,
  // and there is no guarantee of success for either

  for (df <- defs) {
    todo { Process(df) }
  }

  // compute lemmas from E-Graph saturation,
  // given left-hand sides of interest
  def extract() {

  }

  def round() {
    while (pending.nonEmpty) {
      val first = pending.head
      pending = pending.tail

      first match {
        case Process(df) =>
          process(df)

        case FuseAt(df, dg, pos) =>
          fuseAt(df, dg, pos)

        case DeaccumulateAt(df, pos) =>
          deaccumulateAt(df, pos)
      }
    }

    // cleanup here!
  }

  def process(df: Def) {}

  def fuseAt(df: Def, dg: Def, pos: Int) {}

  def deaccumulateAt(df: Def, pos: Int) {}
}

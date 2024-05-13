package cuvee.imp.annotate

import cuvee.ai.Domain
import cuvee.imp._
import cuvee.pure._

class AI[S](domain: Domain[S]) extends Annotate[S] {

  def while_(
      states0: States[S],
      test: Expr,
      body: Prog,
      term: Expr,
      inv: Expr,
      sum: Expr,
      frames: List[Frame]
  ): (States[S], Prog) = {
    val states1 = exec.iter(states0, test, body)
    val states2 = exec.assume(states1, !test)

    val phis =
      for (s <- states1.running)
        yield And(domain.constraints(s))

    val add = Or(phis)
    val inv_ = inv && add
    val prog_ = While(test, body, term, inv_, sum, frames)

    (states2.unbreak, prog_)
  }

  object exec extends Exec[S] with Exec.WithFixpoint[S] {
    def entry(in: List[Var], out: List[Var], spec: Option[Spec]): List[S] =
      domain.entry(in, out, spec)

    def assume(states: List[S], phi: Expr) = {
      // for (s <- states)
      //   yield {
      //     val (s_, _) = domain.assume(s, phi)
      //     s_
      //   }
      ???
    }

    def step(states: List[S], xs: List[Var], rel: Expr) =
      for (s <- states; s_ <- domain.step(s, xs, rel))
        yield s_

    def local(states: List[S], xs: List[Var], rhs: List[Expr]) =
      for (s <- states; s_ <- domain.local(s, xs, rhs))
        yield s_

    def assign(states: List[S], xs: List[Var], rhs: List[Expr]) =
      for (s <- states; s_ <- domain.assign(s, xs, rhs))
        yield s_

    def isSubsetOf(states1: List[S], states2: List[S]) =
      states1 forall { s1 =>
        states2 exists { s2 =>
          domain.subsetOf(s1, s2)
        }
      }

    def widen(states1: List[S], states2: List[S]) =
      ???
      // domain.widen(domain.join(states1), domain.join(states2))

    def narrow(states1: List[S], states2: List[S]) =
      ???
      // domain.narrow(domain.join(states1), domain.join(states2))
  }
}

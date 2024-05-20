package cuvee.imp

import cuvee.pure._

// Semantics of program execution
trait Sem[V, S] {
  // An arbitrary, unconstrained state without any declared variables.
  def arbitrary: S

  // Return a formula that represents the constraints of the given state,
  // may use all those variables that were previously declared and not forgotten since,
  // but auxiliary variables can of course be existentially quantified.
  def constraints(s: S): Expr

  // Even if variables with duplicate names are declared,
  // this methods should return distinct V objects.
  // That means that the return values will be able to distinguish, e.g.,
  // bound or local variables with the same name but in different scopes.
  // Note, args are evaluated without reference to the vs
  def local(vars: Map[Var, V], s: S, xs: List[Var], args: List[Expr]): (List[V], S)

  // Conversely, remove some variables from the state.
  def forget(vars: Map[Var, V], s: S, xs: Set[Var]): S

  // Wwe don't externalize evaluation of expressions, as it is rather specific
  // to the concrete representation (and consistent with assume above).
  def assign(vars: Map[Var, V], s: S, xs: List[Var], args: List[Expr]): S

  // Nondeterministic transition, which modifies the local variables vs,
  // and where Old(_) in rel may refer back to the pre-state of values before the transition
  def step(vars: Map[Var, V], s: S, xs: List[Var], rel: Expr): List[S]

  // If the state becomes inconsistent, this method can return the empty list,
  // and if phi is a disjunction it can possibly split.
  def assume(vars: Map[Var, V], s: S, phi: Expr): List[S]

  // Test whether this state can assert phi, returning
  // - None, if inconclusive
  // - Some(true),  if definitely
  // - Some(false), if there is a counter-example
  def asserts(vars: Map[Var, V], s: S, phi: Expr): Option[Boolean]
}

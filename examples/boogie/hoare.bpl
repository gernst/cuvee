type Var;
type Val;
type Expr;
type State;

data Nat
  = zero | succ(pred: Nat);

data Cmd
  = skip
  | assign(lhs: Var, rhs: Expr)
  | seq(fst: Cmd, snd: Cmd)
  | if_(test: Expr, left: Cmd, right: Cmd)
  | while_(cond: Expr, body: Cmd)
  ;

function eval(expr: Expr, st: State): Val;
function truth(val: Val): bool;
function prop(expr: Expr): [State]bool;

function update(st: State, lhs: Var, rhs: Val): State;
function subst(prop: [State]bool, lhs: Var, rhs: Expr): [State]bool;

function steps(cmd: Cmd, st: State, st_: State): bool;
function iter(n: Nat, test: Expr, cmd: Cmd, st: State, st_: State): bool;

axiom forall expr: Expr, st: State ::
  prop(expr)[st] == truth(eval(expr, st));

axiom forall p: [State]bool, lhs: Var, rhs: Expr, st: State ::
  subst(p, lhs, rhs)[st] == p[update(st, lhs, eval(rhs, st))];

function not_(p: [State]bool): [State]bool;
function and_(p: [State]bool, q: [State]bool): [State]bool;

axiom forall p: [State]bool, st: State ::
  not_(p)[st] == (! p[st]);

axiom forall p: [State]bool, q: [State]bool, st: State ::
  and_(p, q)[st] == (p[st] && q[st]);

axiom forall st: State, st_: State ::
  steps(skip, st, st_)
    == (st_ == st);

axiom forall lhs: Var, rhs: Expr, st: State, st_: State ::
  steps(assign(lhs, rhs), st, st_)
    == (st_ == update(st, lhs, eval(rhs, st)));

axiom forall fst: Cmd, snd: Cmd, st: State, st__: State ::
  steps(seq(fst, snd), st, st__)
    == (exists st_: State :: steps(fst, st, st_) && steps(snd, st_, st__));

axiom forall test: Expr, body: Cmd, st: State, st_: State ::
  iter(zero, test, body, st, st_)
    == (!truth(eval(test, st)) && st_ == st);

axiom forall n: Nat, test: Expr, body: Cmd, st: State, st__: State ::
  iter(succ(n), test, body, st, st__)
    == (truth(eval(test, st)) && exists st_: State :: steps(body, st, st_) && iter(n, test, body, st_, st__));

axiom forall test: Expr, left: Cmd, right: Cmd, st: State, st_: State ::
  steps(if_(test, left, right), st, st_)
    == (    truth(eval(test, st)) && steps(left,  st, st_)
        || !truth(eval(test, st)) && steps(right, st, st_));

axiom forall test: Expr, body: Cmd, st: State, st_: State ::
  steps(while_(test, body), st, st_)
    == exists n: Nat :: iter(n, test, body, st, st_);

function hoare(pre: [State]bool, cmd: Cmd, post: [State]bool): bool {
  forall st: State, st_: State ::
    pre[st] && steps(cmd, st, st_)
      ==> post[st_]
}

lemma forall P: [State]bool ::
  hoare(P, skip, P);

lemma forall lhs: Var, rhs: Expr, P: [State]bool ::
  hoare(subst(P, lhs, rhs), assign(lhs, rhs), P);

lemma forall fst: Cmd, snd: Cmd, P: [State]bool, Q: [State]bool, R: [State]bool ::
  hoare(P, fst, Q) && hoare(Q, snd, R)
    ==> hoare(P, seq(fst, snd), R);

lemma forall test: Expr, left: Cmd, right: Cmd, P: [State]bool, Q: [State]bool ::
  hoare(and_(P, prop(test)), left, Q) &&
  hoare(and_(P, not_(prop(test))), right, Q)
    ==> hoare(P, if_(test, left, right), Q);

lemma forall n: Nat, test: Expr, body: Cmd, st: State, st_: State ::
  iter(n, test, body, st, st_)
    ==> ! truth(eval(test, st_))
proof induction n end;

lemma forall n: Nat, test: Expr, body: Cmd, I: [State]bool, st: State, st_: State ::
  hoare(and_(I, prop(test)), body, I) &&
  iter(n, test, body, st, st_) && I[st]
    ==> I[st_]
proof induction n end;

lemma forall test: Expr, body: Cmd, I: [State]bool ::
  hoare(and_(I, prop(test)), body, I)
    ==> hoare(I, while_(test, body), and_(I, not_(prop(test))));

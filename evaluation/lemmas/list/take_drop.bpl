data nat = zero | succ(pred: nat);

type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function sub(m: nat, n: nat): nat;
function leq(m: nat, n: nat): bool;

axiom forall m: nat ::
  sub(m, zero) == m;
axiom forall m: nat, n: nat ::
  sub(zero, succ(n)) == zero;
axiom forall m: nat, n: nat ::
  sub(succ(m), succ(n)) == sub(m, n);

axiom forall n: nat ::
  leq(zero, n) == true;
axiom forall m: nat ::
  leq(m, zero) == false; // original axiom has leq(cons(m), zero) == false, but that does not simplify leq:1:length
axiom forall m: nat, n: nat ::
  leq(succ(m), succ(n)) == leq(m, n);

function length(xs: list<elem>): nat;
function take(n: nat, xs: list<elem>): list<elem>;
function drop(n: nat, xs: list<elem>): list<elem>;
function map (f: [elem]elem, xs: list<elem>): list<elem>;

function append(xs: list<elem>, ys: list<elem>): list<elem>;
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


axiom
  length(nil) == zero;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == succ(length(xs));

axiom forall n: nat ::
  take(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  take(zero, cons(y, ys)) == nil;
axiom forall n: nat, y: elem, ys: list<elem> ::
  take(succ(n), cons(y, ys)) == cons(y, take(n , ys));

axiom forall n: nat ::
  drop(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  drop(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: elem, ys: list<elem> ::
  drop(succ(n), cons(y, ys)) == drop(n , ys);

axiom forall f: [elem]elem ::
  map(f, nil) == nil;
axiom forall f: [elem]elem, y: elem, ys: list<elem> ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

lemma forall n: nat, xs: list<elem> ::
  append(take(n, xs), drop(n, xs)) == xs
proof induction xs;

lemma forall n: nat, xs: list<elem> ::
  length(drop(n, xs)) == sub(length(xs), n)
proof induction xs;
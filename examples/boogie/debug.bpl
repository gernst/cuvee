type elem;
data nat = zero | succ(pred: nat);
data list<a> = nil | cons(head: a, tail: list<a>);

function add(m: nat, n: nat): nat;
function length(xs: list<elem>): nat;
function reverse(xs: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;

lemma forall m: nat, n: nat ::
  add(m, succ(n)) == succ(add(m, n));

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom
  length(nil) == zero;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == succ(length(xs));

axiom
  reverse(nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil));



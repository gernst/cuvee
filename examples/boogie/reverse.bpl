type elem;
data nat = zero | succ(pred: nat);
data list<a> = nil | cons(head: a, tail: list<a>);

function add(m: nat, n: nat): nat;
function length(xs: list<elem>): nat;
function reverse(xs: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;

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

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function map (f: [elem]elem, xs: list<elem>): list<elem>;
axiom forall f: [elem]elem ::
  map(f, nil) == nil;
axiom forall f: [elem]elem, y: elem, ys: list<elem> ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

function qreverse(xs: list<elem>, ys: list<elem>): list<elem>;
axiom forall zs: list<elem> ::
  qreverse(nil, zs) == zs;
axiom forall zs: list<elem>, y: elem, ys: list<elem> ::
  qreverse(cons(y, ys), zs) == qreverse(ys, cons(y, zs));


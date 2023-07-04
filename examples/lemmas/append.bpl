data nat = zero | succ(pred: nat);

type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function add(m: nat, n: nat): nat;

function append(xs: list<elem>, ys: list<elem>): list<elem>;
function length(xs: list<elem>): nat;
function count(x: elem, xs: list<elem>): nat;

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom
  length(nil) == zero;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == succ(length(xs));

axiom forall x: elem ::
  count(x, nil) == zero;
axiom forall x: elem, y: elem, ys: list<elem> ::
  count(x, cons(y, ys)) == if x == y then succ(count(x, ys)) else count(x, ys);
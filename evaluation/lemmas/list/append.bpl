// characteristic lemmas:
//   snoc can be expressed as append
//   associativity of append
//   distributivity of catamorphisms over append

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

function snoc(xs: list, y: nat): list;
axiom forall z: nat ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: nat, y: nat, ys: list ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function count(x: nat, xs: list): nat;
axiom forall x: nat ::
  count(x, nil) == zero;
axiom forall x: nat, y: nat, ys: list ::
  count(x, cons(y, ys)) == (if x == y then succ(count(x, ys)) else count(x, ys));

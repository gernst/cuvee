// characteristic lemmas:
//    rotate and reverse yield the same result if n is large enough
//    length(reverse(xs)) == length(xs)

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function leq(m: nat, n: nat): bool;
axiom forall n: nat ::
  leq(zero, n) == true;
axiom forall m: nat ::
  leq(succ(m), zero) == false;
axiom forall m: nat, n: nat ::
  leq(succ(m), succ(n)) == leq(m, n);

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));



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



function reverse(xs: list): list;
axiom
  reverse(nil) == nil;
axiom forall y: nat, ys: list ::
  reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil));

function rotate(cnt: nat, xs: list): list;
axiom forall n: nat ::
  rotate(n, nil) == nil;
axiom forall y: nat, ys: list ::
  rotate(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: nat, ys: list ::
  rotate(succ(n), cons(y, ys)) == append(rotate(n, ys), cons(y, nil));

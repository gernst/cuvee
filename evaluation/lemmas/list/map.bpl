// characteristic lemmas
//   length(map(f, xs)) = xs
//   map distributes through append, take, drop

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function map (f: [nat]nat, xs: list): list;
axiom forall f: [nat]nat ::
  map(f, nil) == nil;
axiom forall f: [nat]nat, y: nat, ys: list ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

function take(cnt: nat, xs: list): list;
axiom forall n: nat ::
  take(n, nil) == nil;
axiom forall y: nat, ys: list ::
  take(zero, cons(y, ys)) == nil;
axiom forall n: nat, y: nat, ys: list ::
  take(succ(n), cons(y, ys)) == cons(y, take(n , ys));

function drop(cnt: nat, xs: list): list;
axiom forall n: nat ::
  drop(n, nil) == nil;
axiom forall y: nat, ys: list ::
  drop(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: nat, ys: list ::
  drop(succ(n), cons(y, ys)) == drop(n , ys);

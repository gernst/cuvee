// characteristic lemmas:
//    reverse(reverse(xs)) == xs
//    reverse(append(xs, ys)) == append(reverse(ys), reverse(xs)) or similar
//    relations between reverse/nreverse/qreverse

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


function reverse(xs: list): list;
axiom
  reverse(nil) == nil;
axiom forall y: nat, ys: list ::
  reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil));

function qreverse(xs: list, ys: list): list;
axiom forall zs: list ::
  qreverse(nil, zs) == zs;
axiom forall zs: list, y: nat, ys: list ::
  qreverse(cons(y, ys), zs) == qreverse(ys, cons(y, zs));

function nreverse(xs: list, ys: list): list;
axiom forall zs: list ::
  nreverse(nil, zs) == zs;
axiom forall zs: list, y: nat, ys: list ::
  nreverse(cons(y, ys), zs) == append(nreverse(ys, zs), cons(y, nil));



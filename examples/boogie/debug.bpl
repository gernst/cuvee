
data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);


function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


function take(cnt: nat, xs: list): list;
axiom forall n: nat ::
  take(n, nil) == nil;
axiom forall y: nat, ys: list ::
  take(zero, cons(y, ys)) == nil;
axiom forall n: nat, y: nat, ys: list ::
  take(succ(n), cons(y, ys)) == cons(y, take(n , ys));
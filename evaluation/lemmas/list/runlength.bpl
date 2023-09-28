// characteristic lemmas
//    sum over append
//    sum(decode(ind, val)) = sumruns(ind, val) under suitable precondition
data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

function mul(m: nat, n: nat): nat;
axiom forall n: nat ::
  mul(zero, n) == zero;
axiom forall m: nat, n: nat ::
  mul(succ(m), n) == add(n, mul(m, n));

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


function sum(xs: list): nat;
axiom
    sum(nil) == zero;
axiom forall n: nat, xs: list ::
    sum(cons(n,xs)) == add(n, sum(xs));

function is_runs(ind: list, val: list): bool;
axiom
    is_runs(nil, nil) == true;
axiom forall n: nat, ind: list, x: nat, val: list ::
    is_runs(cons(n,ind), cons(x, val)) == is_runs(ind, val);
axiom forall n: nat, ind: list ::
    is_runs(cons(n,ind), nil) == false;
axiom forall ind: list, x: nat, val: list ::
    is_runs(nil, cons(x, val)) == false;

function sumruns(ind: list, val: list): nat;
axiom
    sumruns(nil, nil) == zero;
axiom forall n: nat, ind: list, x: nat, val: list ::
    sumruns(cons(n,ind), cons(x, val)) == add(mul(n, x), sumruns(ind, val));
axiom forall n: nat, ind: list ::
    sumruns(cons(n,ind), nil) == zero;
axiom forall ind: list, x: nat, val: list ::
    sumruns(nil, cons(x, val)) == zero;
  
function decode(ind: list, val: list): list;
axiom
    decode(nil, nil) == nil;
axiom forall ind: list, x: nat, val: list ::
    decode(cons(zero, ind), cons(x, val)) == decode(ind, val);
axiom forall n: nat, ind: list, x: nat, val: list ::
    decode(cons(succ(n), ind), cons(x, val)) == cons(x, decode(cons(n, ind), cons(x, val)));
axiom forall n: nat, ind: list, x: nat, val: list ::
    decode(cons(n,ind), nil) == nil;
axiom forall n: nat, ind: list, x: nat, val: list ::
    decode(nil, cons(x, val)) == nil;
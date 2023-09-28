data nat = zero | succ(pred: nat);

data list<a> = nil | cons(head: a, tail: list<a>);

function add(m: nat, n: nat): nat;
function mul(m: nat, n: nat): nat;

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom forall n: nat ::
  mul(zero, n) == zero;
axiom forall m: nat, n: nat ::
  mul(succ(m), n) == add(n, mul(m, n));

function decode(ind: list<nat>, val: list<nat>): list<nat>;
function sum(xs: list<nat>): nat;
function sumruns(ind: list<nat>, val: list<nat>): nat;

axiom
    sum(nil) == zero;
axiom forall n: nat, xs: list<nat> ::
    sum(cons(n,xs)) == add(n, sum(xs));

axiom
    sumruns(nil, nil) == zero;
axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    sumruns(cons(n,ind), cons(x, val)) == add(mul(n, x), sumruns(ind, val));

axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    sumruns(cons(n,ind), nil) == zero;
axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    sumruns(nil, cons(x, val)) == zero;
  

axiom
    decode(nil, nil) == nil;
axiom forall ind: list<nat>, x: nat, val: list<nat> ::
    decode(cons(zero, ind), cons(x, val)) == decode(ind, val);
axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    decode(cons(succ(n), ind), cons(x, val)) == cons(x, decode(cons(n, ind), cons(x, val)));

axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    decode(cons(n,ind), nil) == nil;
axiom forall n: nat, ind: list<nat>, x: nat, val: list<nat> ::
    decode(nil, cons(x, val)) == nil;
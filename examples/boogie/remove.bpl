data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

function sub(m: nat, n: nat): nat;
axiom forall m: nat ::
  sub(m, zero) == m;
axiom forall n: nat ::
  sub(zero, succ(n)) == zero;
axiom forall m: nat, n: nat ::
  sub(succ(m), succ(n)) == sub(m, n);

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function contains(x: nat, xs: list): bool;
axiom forall x: nat ::
  contains(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

function remove(x: nat, xs: list): list;
axiom forall x: nat ::
  remove(x, nil) == nil;
axiom forall x: nat, y: nat, ys: list ::
  remove(x, cons(y, ys)) == if x == y then remove(x, ys) else cons(y, remove(x, ys));

function count(x: nat, xs: list): nat;
axiom forall x: nat ::
  count(x, nil) == zero;
axiom forall x: nat, y: nat, ys: list ::
  count(x, cons(y, ys)) == if x == y then succ(count(x, ys)) else count(x, ys);
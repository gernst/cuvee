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

function contains(x: nat, xs: list): bool;
axiom forall x: nat ::
  contains(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

function contains_(x: nat, xs: list): bool;
axiom forall x: nat ::
  contains_(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains_(x, cons(y, ys)) ==
    if x == y then true else contains_(x, ys);

function insert(x: nat, xs: list): list {
  cons(x, xs)
}


function adjoin(x: nat, xs: list): list;
axiom forall x: nat ::
  adjoin(x, nil) == cons(x, nil);
axiom forall x: nat, y: nat, ys: list ::
  adjoin(x, cons(y, ys)) == 
    if x == y then cons(y, ys) else cons(y, adjoin(x, ys));

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function removefirst(x: nat, xs: list): list;
axiom forall x: nat ::
  removefirst(x, nil) == nil;
axiom forall x: nat, y: nat, ys: list ::
  removefirst(x, cons(y, ys)) == if x == y then ys else cons(y, removefirst(x, ys));

function removeall(x: nat, xs: list): list;
axiom forall x: nat ::
  removeall(x, nil) == nil;
axiom forall x: nat, y: nat, ys: list ::
  removeall(x, cons(y, ys)) == if x == y then removeall(x, ys) else cons(y, removeall(x, ys));
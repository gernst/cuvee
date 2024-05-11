data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

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

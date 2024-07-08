data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function contains(x: nat, xs: list): bool;
axiom forall x: nat ::
  contains(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

function insert(x: nat, xs: list): list {
  cons(x, xs)
}

function adjoin(x: nat, xs: list): list {
  if(contains(x, xs)) then xs else cons(x, xs)
}

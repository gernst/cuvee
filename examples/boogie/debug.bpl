data nat
  = zero | succ(pred: nat);

function add(x: nat, y: nat): nat;

axiom forall y: nat ::
  add(zero, y) == y;
axiom forall x: nat, y : nat ::
  add(succ(x), y) == succ(add(x, y));
data nat
  = zero | succ(pred: nat);

function minus(x: nat, y: nat): nat;

axiom forall y: nat ::
  minus(zero, y) == zero;
axiom forall z: nat ::
  minus(succ(z), zero) == succ(z);
axiom forall z: nat, y2: nat ::
  minus(succ(z), succ(y2)) == minus(z, y2);
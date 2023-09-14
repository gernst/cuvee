data nat
  = zero | succ(pred: nat);

function minus(x: nat, y: nat): nat;

axiom forall y: nat ::
  minus(zero, y) == zero;
axiom forall z: nat ::
  minus(succ(z), zero) == succ(z);
axiom forall z: nat, y2: nat ::
  minus(succ(z), succ(y2)) == minus(z, y2);

function minus2(x: nat, y: nat): nat;

axiom forall y5: nat ::
  minus2(zero, y5) == zero;
axiom forall z3: nat ::
  minus2(succ(z3), zero) == succ(z3);
axiom forall z7: nat, y22: nat ::
  minus2(succ(z7), succ(y22)) == minus2(z7, y22);
data nat = zero | succ(pred: nat);

function add(m: nat, n: nat): nat;
// function sub(m: nat, n: nat): nat;
// function mul(m: nat, n: nat): nat;

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

// axiom forall m: nat ::
//   sub(m, zero) == m;
// axiom forall m: nat, n: nat ::
//   sub(succ(m), succ(n)) == sub(m, n);

// axiom forall n: nat ::
//   mul(zero, n) == zero;
// axiom forall m: nat, n: nat ::
//   mul(succ(m), n) == add(mul(m, n), n);
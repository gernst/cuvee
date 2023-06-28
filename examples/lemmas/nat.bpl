data nat = zero | succ(pred: nat);

function add(m: nat, n: nat): nat;
function sub(m: nat, n: nat): nat;
function mul(m: nat, n: nat): nat;

function leq(m: nat, n: nat): bool;

axiom forall n: nat ::
  leq(zero, n) == true;
axiom forall m: nat ::
  leq(succ(m), zero) == false;
axiom forall m: nat, n: nat ::
  leq(succ(m), succ(n)) == leq(m, n);

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom forall m: nat ::
  sub(m, zero) == m;
axiom forall n: nat ::
  sub(zero, succ(n)) == zero;
axiom forall m: nat, n: nat ::
  sub(succ(m), succ(n)) == sub(m, n);

axiom forall n: nat ::
  mul(zero, n) == zero;
axiom forall m: nat, n: nat ::
  mul(succ(m), n) == add(n, mul(m, n));

lemma forall n: nat ::
  sub(zero, n) == zero;
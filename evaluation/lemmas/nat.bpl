data nat = zero | succ(pred: nat);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true) == false;

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

function mul(m: nat, n: nat): nat;
axiom forall n: nat ::
  mul(zero, n) == zero;
axiom forall m: nat, n: nat ::
  mul(succ(m), n) == add(n, mul(m, n));

function leq(m: nat, n: nat): bool;
axiom forall n: nat ::
  leq(zero, n) == true;
axiom forall m: nat ::
  leq(succ(m), zero) == false;
axiom forall m: nat, n: nat ::
  leq(succ(m), succ(n)) == leq(m, n);

function lt(m: nat, n: nat): bool;
axiom forall m: nat ::
  lt(m, zero) == false;
axiom forall n: nat ::
  lt(zero, succ(n)) == true;
axiom forall m: nat, n: nat ::
  lt(succ(m), succ(n)) == lt(m, n);

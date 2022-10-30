data nat = zero | succ(n: nat);

function add(a: nat, b: nat): nat;
function mul(a: nat, b: nat): nat;

axiom forall b: nat ::
    add(zero, b) == b;
axiom forall a: nat, b: nat ::
    add(succ(a), b) == succ(add(a, b));

axiom forall b: nat ::
    mul(zero, b) == zero;
axiom forall a: nat, b: nat ::
    mul(succ(a), b) == add(b, mul(a, b));

// lemmas about add
lemma forall a: nat ::
    add(a, zero) == a
proof
    induction a end;

lemma forall a: nat, b: nat ::
    add(a, succ(b)) == succ(add(a, b))
proof
    induction a end;

// add is commutative
lemma forall a: nat, b: nat ::
    add(a, b) == add(b, a)
proof
    induction a end;

// add is associative
lemma forall a: nat, b: nat, c: nat ::
    add(a, add(b, c)) == add(add(a, b), c)
proof
    induction a end;

// lemmas about mul
lemma forall a: nat ::
    mul(a, zero) == zero
proof
    induction a end;

lemma forall a: nat, b: nat ::
    mul(a, succ(b)) == add(mul(a, b), a)
proof
    induction a end;

// mul is commutative
lemma forall a: nat, b: nat ::
    mul(a, b) == mul(b, a)
proof
    induction a end;

// add, mul are distributive
lemma forall a: nat, b: nat, c:nat ::
    mul(a, add(b, c)) == add(mul(a, b), mul(a, c))
proof
    induction a end;

// mul is associative
lemma forall a: nat, b: nat, c: nat ::
    mul(a, mul(b, c)) == mul(mul(a, b), c)
proof
    induction a end;

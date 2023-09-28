data nat = zero | succ(pred: nat);
function not_(x₀: Bool): Bool;
axiom (not_(false) <==> true);
axiom (not_(true) <==> false);
function add(x₀: nat, x₁: nat): nat;
axiom forall n: nat :: (add(zero, n) == n);
axiom forall m: nat, n: nat :: (add(succ(m), n) == succ(add(m, n)));
function sub(x₀: nat, x₁: nat): nat;
axiom forall m: nat :: (sub(m, zero) == m);
axiom forall n: nat :: (sub(zero, succ(n)) == zero);
axiom forall m: nat, n: nat :: (sub(succ(m), succ(n)) == sub(m, n));
function mul(x₀: nat, x₁: nat): nat;
axiom forall n: nat :: (mul(zero, n) == zero);
axiom forall m: nat, n: nat :: (mul(succ(m), n) == add(n, mul(m, n)));
function leq(x₀: nat, x₁: nat): Bool;
axiom forall n: nat :: (leq(zero, n) <==> true);
axiom forall m: nat :: (leq(succ(m), zero) <==> false);
axiom forall m: nat, n: nat :: (leq(succ(m), succ(n)) <==> leq(m, n));
function lt(x₀: nat, x₁: nat): Bool;
axiom forall m: nat :: (lt(m, zero) <==> false);
axiom forall n: nat :: (lt(zero, succ(n)) <==> true);
axiom forall m: nat, n: nat :: (lt(succ(m), succ(n)) <==> lt(m, n));
lemma forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)));
lemma forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(sub(y₁, y₀), sub(zero, y₀)));
lemma forall y₀: nat, x₁: nat :: (leq(succ(y₀), x₁) <==> lt(zero, sub(x₁, y₀)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁));
lemma forall y₀: nat, x₁: nat :: (add(y₀, x₁) == add(y₀, add(x₁, zero)));
lemma forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀));
lemma forall y₀: nat, x₁: nat :: (leq(succ(y₀), x₁) <==> lt(sub(zero, y₀), sub(x₁, y₀)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)));
lemma forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(y₀, x₀), mul(x₀, y₁)));
lemma forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(add(x₀, zero), mul(y₀, x₀)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(mul(y₀, y₁), x₁) == add(add(x₁, zero), mul(y₁, y₀)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == mul(x₁, add(y₁, y₀)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, mul(y₀, y₁)) == mul(mul(x₀, y₁), add(y₀, zero)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (mul(mul(y₀, y₁), x₁) == mul(mul(x₁, y₁), y₀));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (mul(mul(y₀, y₁), x₁) == mul(mul(y₁, y₀), x₁));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, sub(y₀, y₁)) == mul(sub(y₀, y₁), x₀));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (sub(mul(y₀, y₁), x₁) == sub(mul(y₁, y₀), add(x₁, zero)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (sub(mul(y₀, y₁), x₁) == sub(mul(y₁, y₀), x₁));

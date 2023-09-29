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
lemma forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)));
lemma forall y₀: Bool :: (not_(not_(y₀)) <==> y₀);
lemma forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀));
lemma forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀));
lemma forall x: nat :: (add(x, zero) == x);

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
function add(x₀: nat, x₁: nat): nat;
axiom forall n: nat :: (add(zero, n) == n);
axiom forall m: nat, n: nat :: (add(succ(m), n) == succ(add(m, n)));
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function qlength(x₀: list, x₁: nat): nat;
axiom forall n: nat :: (qlength(nil, n) == n);
axiom forall x: nat, xs: list, n: nat :: (qlength(cons(x, xs), n) == qlength(xs, succ(n)));
function nlength(x₀: list, x₁: nat): nat;
axiom forall n: nat :: (nlength(nil, n) == n);
axiom forall x: nat, xs: list, n: nat :: (nlength(cons(x, xs), n) == succ(nlength(xs, n)));
lemma forall y₀: list, y₁: nat, x₁: nat :: (add(nlength(y₀, y₁), x₁) == nlength(y₀, add(y₁, x₁)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)));
lemma forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == nlength(y₀, x₁));
lemma forall x: nat :: (add(x, zero) == x);
lemma forall x: list, z₀: nat :: ((zero == z₀) ==> (length(x) == nlength(x, z₀)));

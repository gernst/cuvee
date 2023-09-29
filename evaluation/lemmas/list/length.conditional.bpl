data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function qlength(x₀: list, x₁: nat): nat;
axiom forall n: nat :: (qlength(nil, n) == n);
axiom forall x: nat, xs: list, n: nat :: (qlength(cons(x, xs), n) == qlength(xs, succ(n)));
function nlength(x₀: list, x₁: nat): nat;
axiom forall n: nat :: (nlength(nil, n) == n);
axiom forall x: nat, xs: list, n: nat :: (nlength(cons(x, xs), n) == succ(nlength(xs, n)));
lemma forall x: list, z₀: nat :: ((zero == z₀) ==> (length(x) == nlength(x, z₀)));

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
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
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function contains(x₀: nat, x₁: list): Bool;
axiom forall x: nat :: (contains(x, nil) <==> false);
axiom forall x: nat, y: nat, ys: list :: (contains(x, cons(y, ys)) <==> ((x == y) || contains(x, ys)));
function remove(x₀: nat, x₁: list): list;
axiom forall x: nat :: (remove(x, nil) == nil);
axiom forall x: nat, y: nat, ys: list :: (remove(x, cons(y, ys)) == (if (x == y) then remove(x, ys) else cons(y, remove(x, ys))));
function count(x₀: nat, x₁: list): nat;
axiom forall x: nat :: (count(x, nil) == zero);
axiom forall x: nat, y: nat, ys: list :: (count(x, cons(y, ys)) == (if (x == y) then succ(count(x, ys)) else count(x, ys)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)));
lemma forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂));
lemma forall y₀: Bool :: (not_(not_(y₀)) <==> y₀);
lemma forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁));
lemma forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero));
lemma forall x: nat :: (add(x, zero) == x);

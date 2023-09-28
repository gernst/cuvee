data nat = zero | succ(pred: nat);
data list = nil | cons(head: list, tail: list);
function add(x₀: nat, x₁: nat): nat;
axiom forall n: nat :: (add(zero, n) == n);
axiom forall m: nat, n: nat :: (add(succ(m), n) == succ(add(m, n)));
function snoc(x₀: list, x₁: nat): list;
axiom forall z: nat :: (snoc(nil, z) == cons(z, nil));
axiom forall z: nat, y: nat, ys: list :: (snoc(cons(y, ys), z) == cons(y, snoc(ys, z)));
function append(x₀: list, x₁: list): list;
axiom forall ys: list :: (append(nil, ys) == ys);
axiom forall x: nat, xs: list, ys: list :: (append(cons(x, xs), ys) == cons(x, append(xs, ys)));
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function count(x₀: nat, x₁: list): nat;
axiom forall x: nat :: (count(x, nil) == zero);
axiom forall x: nat, y: nat, ys: list :: (count(x, cons(y, ys)) == (if (x == y) then succ(count(x, ys)) else count(x, ys)));
lemma forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)));
lemma forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))));
lemma forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)));
lemma forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)));
lemma forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)));
lemma forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))));
lemma forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)));
lemma forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)));
lemma forall x: list :: (append(x, nil) == x);
lemma forall x: nat :: (add(x, zero) == x);

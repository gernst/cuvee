data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
function leq(x₀: nat, x₁: nat): Bool;
axiom forall n: nat :: (leq(zero, n) <==> true);
axiom forall m: nat :: (leq(succ(m), zero) <==> false);
axiom forall m: nat, n: nat :: (leq(succ(m), succ(n)) <==> leq(m, n));
function lt(x₀: nat, x₁: nat): Bool;
axiom forall m: nat :: (lt(m, zero) <==> false);
axiom forall n: nat :: (lt(zero, succ(n)) <==> true);
axiom forall m: nat, n: nat :: (lt(succ(m), succ(n)) <==> lt(m, n));
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function append(x₀: list, x₁: list): list;
axiom forall ys: list :: (append(nil, ys) == ys);
axiom forall x: nat, xs: list, ys: list :: (append(cons(x, xs), ys) == cons(x, append(xs, ys)));
function map(x₀: [nat]nat, x₁: list): list;
axiom forall f: [nat]nat :: (map(f, nil) == nil);
axiom forall f: [nat]nat, y: nat, ys: list :: (map(f, cons(y, ys)) == cons(f[y], map(f, ys)));
function take(x₀: nat, x₁: list): list;
axiom forall n: nat :: (take(n, nil) == nil);
axiom forall y: nat, ys: list :: (take(zero, cons(y, ys)) == nil);
axiom forall n: nat, y: nat, ys: list :: (take(succ(n), cons(y, ys)) == cons(y, take(n, ys)));
function drop(x₀: nat, x₁: list): list;
axiom forall n: nat :: (drop(n, nil) == nil);
axiom forall y: nat, ys: list :: (drop(zero, cons(y, ys)) == cons(y, ys));
axiom forall n: nat, y: nat, ys: list :: (drop(succ(n), cons(y, ys)) == drop(n, ys));
lemma forall x₀: list, y₀: nat, y₁: list :: (append(x₀, drop(y₀, y₁)) == append(append(x₀, nil), drop(y₀, y₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁));
lemma forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, drop(zero, x₁)));
lemma forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)));
lemma forall y₀: nat, x₁: nat :: (leq(succ(y₀), x₁) <==> lt(y₀, x₁));
lemma forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(append(y₀, y₁), append(x₁, nil)));
lemma forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁));
lemma forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, drop(y₀, y₁)) == drop(y₀, map(x₀, y₁)));
lemma forall y₀: nat, x₁: list :: (drop(succ(y₀), x₁) == drop(succ(zero), drop(y₀, x₁)));
lemma forall x₀: list, y₀: [nat]nat, y₁: list :: (append(x₀, map(y₀, y₁)) == append(drop(zero, x₀), map(y₀, y₁)));
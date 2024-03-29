data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
function leq(x₀: nat, x₁: nat): Bool;
axiom forall n: nat :: (leq(zero, n) <==> true);
axiom forall m: nat :: (leq(succ(m), zero) <==> false);
axiom forall m: nat, n: nat :: (leq(succ(m), succ(n)) <==> leq(m, n));
function add(x₀: nat, x₁: nat): nat;
axiom forall n: nat :: (add(zero, n) == n);
axiom forall m: nat, n: nat :: (add(succ(m), n) == succ(add(m, n)));
function append(x₀: list, x₁: list): list;
axiom forall ys: list :: (append(nil, ys) == ys);
axiom forall x: nat, xs: list, ys: list :: (append(cons(x, xs), ys) == cons(x, append(xs, ys)));
function length(x₀: list): nat;
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
function reverse(x₀: list): list;
axiom (reverse(nil) == nil);
axiom forall y: nat, ys: list :: (reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil)));
function rotate(x₀: nat, x₁: list): list;
axiom forall n: nat :: (rotate(n, nil) == nil);
axiom forall y: nat, ys: list :: (rotate(zero, cons(y, ys)) == cons(y, ys));
axiom forall n: nat, y: nat, ys: list :: (rotate(succ(n), cons(y, ys)) == append(rotate(n, ys), cons(y, nil)));
lemma forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)));
lemma forall x₀: list, y₀: nat, y₁: list :: (append(x₀, rotate(y₀, y₁)) == append(append(x₀, nil), rotate(y₀, y₁)));
lemma forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == append(rotate(zero, x₀), cons(y₀, y₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁));
lemma forall y₀: nat :: (y₀ == add(y₀, zero));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), rotate(zero, y₁)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁));
lemma forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀));
lemma forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)));
lemma forall y₀: nat, y₁: list, x₁: list :: (append(rotate(y₀, y₁), x₁) == append(rotate(y₀, y₁), append(x₁, nil)));
lemma forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, rotate(zero, x₁)));
lemma forall y₀: list :: (length(reverse(y₀)) == length(y₀));
lemma forall x₁: list :: (x₁ == append(x₁, nil));
lemma forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(rotate(zero, x₀), reverse(y₀)));
lemma forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == rotate(length(y₁), cons(y₀, y₁)));
lemma forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)));
lemma forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)));
lemma forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, rotate(zero, y₀)));

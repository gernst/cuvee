data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);
function append(x₀: list, x₁: list): list;
axiom forall ys: list :: (append(nil, ys) == ys);
axiom forall x: nat, xs: list, ys: list :: (append(cons(x, xs), ys) == cons(x, append(xs, ys)));
function reverse(x₀: list): list;
axiom (reverse(nil) == nil);
axiom forall y: nat, ys: list :: (reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil)));
function qreverse(x₀: list, x₁: list): list;
axiom forall zs: list :: (qreverse(nil, zs) == zs);
axiom forall zs: list, y: nat, ys: list :: (qreverse(cons(y, ys), zs) == qreverse(ys, cons(y, zs)));
function nreverse(x₀: list, x₁: list): list;
axiom forall zs: list :: (nreverse(nil, zs) == zs);
axiom forall zs: list, y: nat, ys: list :: (nreverse(cons(y, ys), zs) == append(nreverse(ys, zs), cons(y, nil)));
lemma forall x₁: list :: (x₁ == append(x₁, nil));
lemma forall y₀: list :: (reverse(y₀) == nreverse(y₀, nil));
lemma forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)));
lemma forall x₀: list, y₀: list :: (qreverse(x₀, reverse(y₀)) == append(qreverse(x₀, nil), qreverse(y₀, nil)));
lemma forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == qreverse(y₁, cons(y₀, nil)));
lemma forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == nreverse(y₀, cons(x₀, nil)));
lemma forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, append(y₀, y₁)) == qreverse(qreverse(y₀, x₀), y₁));
lemma forall y₀: list, y₁: list :: (reverse(nreverse(y₀, y₁)) == qreverse(reverse(y₀), reverse(y₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)));
lemma forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(append(y₀, nil), x₁));
lemma forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == qreverse(reverse(x₀), qreverse(y₀, nil)));
lemma forall x₀: list, y₀: list :: (nreverse(x₀, reverse(y₀)) == qreverse(append(y₀, nil), nreverse(x₀, nil)));
lemma forall y₀: list, y₁: list, x₁: list :: (qreverse(append(y₀, y₁), x₁) == qreverse(y₁, qreverse(y₀, x₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, nreverse(y₀, y₁)) == nreverse(nreverse(y₁, y₀), qreverse(x₀, nil)));
lemma forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == qreverse(qreverse(y₁, nil), qreverse(y₀, x₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, append(y₀, y₁)) == append(append(y₀, y₁), nreverse(x₀, nil)));
lemma forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == qreverse(nreverse(x₀, nil), cons(y₀, y₁)));
lemma forall x₀: nat, y₀: list, y₁: list :: (cons(x₀, append(y₀, y₁)) == nreverse(qreverse(y₁, nil), cons(x₀, y₀)));
lemma forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == nreverse(append(y₀, nil), nreverse(y₁, nil)));
lemma forall y₀: list, y₁: list, x₁: list :: (qreverse(nreverse(y₀, y₁), x₁) == append(y₀, qreverse(y₁, x₁)));
lemma forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == qreverse(nreverse(x₁, y₁), nreverse(y₀, nil)));
lemma forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, qreverse(y₀, y₁)) == append(reverse(y₀), nreverse(x₀, y₁)));
lemma forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, qreverse(y₀, y₁)) == nreverse(qreverse(y₁, y₀), qreverse(x₀, nil)));
lemma forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == nreverse(qreverse(x₁, y₀), y₁));

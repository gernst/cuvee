data nat = zero | succ(n: nat);
data list = nil | cons(head: nat, tail: list);
data tree = leaf | node(value: nat, left: tree, right: tree);
function add(x₀: nat, x₁: nat): nat;
function length(x₀: list): nat;
function map(x₀: [nat]nat, x₁: list): list;
function append(x₀: list, x₁: list): list;
function contains(x₀: nat, x₁: list): Bool;
function size(x₀: tree): nat;
function elems(x₀: tree): list;
function mirror(x₀: tree): tree;
function maptree(x₀: [nat]nat, x₁: tree): tree;
function containstree(x₀: nat, x₁: tree): Bool;
function insert(x₀: nat, x₁: tree): tree;
axiom forall n: nat :: (add(zero, n) == n);
axiom forall m: nat, n: nat :: (add(succ(m), n) == succ(add(m, n)));
axiom (length(nil) == zero);
axiom forall x: nat, xs: list :: (length(cons(x, xs)) == succ(length(xs)));
axiom forall f: [nat]nat :: (map(f, nil) == nil);
axiom forall f: [nat]nat, y: nat, ys: list :: (map(f, cons(y, ys)) == cons(f[y], map(f, ys)));
axiom forall ys: list :: (append(nil, ys) == ys);
axiom forall x: nat, xs: list, ys: list :: (append(cons(x, xs), ys) == cons(x, append(xs, ys)));
axiom forall x: nat :: (contains(x, nil) <==> false);
axiom forall x: nat, y: nat, ys: list :: (contains(x, cons(y, ys)) <==> ((x == y) || contains(x, ys)));
axiom (size(leaf) == zero);
axiom forall v: nat, l: tree, r: tree :: (size(node(v, l, r)) == succ(add(size(l), size(r))));
axiom (mirror(leaf) == leaf);
axiom forall v: nat, l: tree, r: tree :: (mirror(node(v, l, r)) == node(v, r, l));
axiom forall f: [nat]nat :: (maptree(f, leaf) == leaf);
axiom forall f: [nat]nat, v: nat, l: tree, r: tree :: (maptree(f, node(v, l, r)) == node(f[v], maptree(f, l), maptree(f, r)));
axiom (elems(leaf) == nil);
axiom forall v: nat, l: tree, r: tree :: (elems(node(v, l, r)) == cons(v, append(elems(l), elems(r))));
axiom forall x: nat :: (containstree(x, leaf) <==> false);
axiom forall x: nat, v: nat, l: tree, r: tree :: (containstree(x, node(v, l, r)) <==> ((x == v) || containstree(x, l) || containstree(x, r)));
axiom forall x: nat :: (insert(x, leaf) == node(x, leaf, leaf));
axiom forall x: nat, v: nat, l: tree, r: tree :: (insert(x, node(v, l, r)) == node(v, insert(x, l), r));
lemma forall y₀: nat :: (y₀ == add(y₀, zero));
lemma forall x₁: list :: (x₁ == append(x₁, nil));
lemma forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)));
lemma forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)));
lemma forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)));
lemma forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)));
lemma forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)));
lemma forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == add(size(y₁), zero));
lemma forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)));
lemma forall y₀: nat, y₁: tree :: (size(insert(y₀, y₁)) == size(insert(zero, y₁)));
lemma forall y₀: [nat]nat, y₁: tree :: (elems(maptree(y₀, y₁)) == map(y₀, elems(y₁)));
lemma forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)));
lemma forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁));
lemma forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == length(elems(y₁)));
lemma forall y₀: tree :: (succ(size(y₀)) == size(insert(zero, y₀)));
lemma forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)));
lemma forall y₀: tree :: (length(elems(y₀)) == size(y₀));
lemma forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)));
lemma forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)));
lemma forall y₀: tree :: (mirror(mirror(y₀)) == y₀);
lemma forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)));
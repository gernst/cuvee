data nat  = zero | succ(n: nat);
data list = nil  | cons(head: nat, tail: list);
data tree = leaf | node(value: nat, left: tree, right: tree);

function add(m: nat, n: nat): nat;

function length(xs: list): nat;
function map (f: [nat]nat, xs: list): list;
function append(xs: list, ys: list): list;
function contains(x: nat, xs: list): bool;

function size(xs: tree): nat;
function elems(t: tree): list;
function mirror(t: tree): tree;
function maptree (f: [nat]nat, t: tree): tree;
function containstree(x: nat, xs: tree): bool;

function insert(x: nat, t: tree): tree;

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

axiom forall f: [nat]nat ::
  map(f, nil) == nil;
axiom forall f: [nat]nat, y: nat, ys: list ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall x: nat ::
  contains(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom
  size(leaf) == zero;
axiom forall v: nat, l: tree, r: tree ::
  size(node(v, l, r)) == succ(add(size(l), size(r)));

axiom
  mirror(leaf) == leaf;
axiom forall v: nat, l: tree, r: tree ::
  mirror(node(v, l, r)) == node(v, r, l);

axiom forall f: [nat]nat ::
  maptree(f, leaf) == leaf;
axiom forall f: [nat]nat, v: nat, l: tree, r: tree ::
  maptree(f, node(v, l, r)) == node(f[v], maptree(f, l), maptree(f, r));

axiom
  elems(leaf) == nil;
axiom forall v: nat, l: tree, r: tree ::
  elems(node(v, l, r)) == cons(v, append(elems(l), elems(r)));
  
axiom forall x: nat ::
  containstree(x, leaf) == false;
axiom forall x: nat, v: nat, l: tree, r: tree ::
  containstree(x, node(v, l, r)) == (x == v || containstree(x, l) || containstree(x, r));

axiom forall x: nat ::
  insert(x, leaf) == node(x, leaf, leaf);
axiom forall x: nat, v: nat, l: tree, r: tree ::
  insert(x, node(v, l, r)) == node(v, insert(x, l), r);
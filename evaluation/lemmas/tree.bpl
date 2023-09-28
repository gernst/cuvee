data Nat  = zero | succ(n: Nat);
data Lst  = nil  | cons(head: Nat, tail: Lst);
data Tree = leaf | node(value: Nat, left: Tree, right: Tree);

function add(m: Nat, n: Nat): Nat;

function length(xs: Lst): Nat;
function map (f: [Nat]Nat, xs: Lst): Lst;
function append(xs: Lst, ys: Lst): Lst;
function contains(x: Nat, xs: Lst): bool;

function size(xs: Tree): Nat;
function elems(t: Tree): Lst;
function mirror(t: Tree): Tree;
function maptree (f: [Nat]Nat, t: Tree): Tree;
function containstree(x: Nat, xs: Tree): bool;

function insert(x: Nat, t: Tree): Tree;

axiom forall n: Nat ::
  add(zero, n) == n;
axiom forall m: Nat, n: Nat ::
  add(succ(m), n) == succ(add(m, n));

axiom
  length(nil) == zero;
axiom forall x: Nat, xs: Lst ::
  length(cons(x,xs)) == succ(length(xs));

axiom forall f: [Nat]Nat ::
  map(f, nil) == nil;
axiom forall f: [Nat]Nat, y: Nat, ys: Lst ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

axiom forall ys: Lst ::
  append(nil, ys) == ys;
axiom forall x: Nat, xs: Lst, ys: Lst ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall x: Nat ::
  contains(x, nil) == false;
axiom forall x: Nat, y: Nat, ys: Lst ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom
  size(leaf) == zero;
axiom forall v: Nat, l: Tree, r: Tree ::
  size(node(v, l, r)) == succ(add(size(l), size(r)));

axiom
  mirror(leaf) == leaf;
axiom forall v: Nat, l: Tree, r: Tree ::
  mirror(node(v, l, r)) == node(v, r, l);

axiom forall f: [Nat]Nat ::
  maptree(f, leaf) == leaf;
axiom forall f: [Nat]Nat, v: Nat, l: Tree, r: Tree ::
  maptree(f, node(v, l, r)) == node(f[v], maptree(f, l), maptree(f, r));

axiom
  elems(leaf) == nil;
axiom forall v: Nat, l: Tree, r: Tree ::
  elems(node(v, l, r)) == cons(v, append(elems(l), elems(r)));
  
axiom forall x: Nat ::
  containstree(x, leaf) == false;
axiom forall x: Nat, v: Nat, l: Tree, r: Tree ::
  containstree(x, node(v, l, r)) == (x == v || containstree(x, l) || containstree(x, r));

axiom forall x: Nat ::
  insert(x, leaf) == node(x, leaf, leaf);
axiom forall x: Nat, v: Nat, l: Tree, r: Tree ::
  insert(x, node(v, l, r)) == node(v, insert(x, l), r);
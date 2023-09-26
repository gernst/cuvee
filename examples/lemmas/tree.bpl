// type Elem;

data Elem = zero | succ(n: Elem);

data Lst<a> = nil  | cons(head: a, tail: Lst<a>);
data Tree<a> = leaf | node(value: a, left: Tree<a>, right: Tree<a>);

function length(xs: Lst<Elem>): int;
function map (f: [Elem]Elem, xs: Lst<Elem>): Lst<Elem>;
function append(xs: Lst<Elem>, ys: Lst<Elem>): Lst<Elem>;
function contains(x: Elem, xs: Lst<Elem>): bool;

function size(xs: Tree<Elem>): int;
function elems(t: Tree<Elem>): Lst<Elem>;
function mirror(t: Tree<Elem>): Tree<Elem>;
function maptree (f: [Elem]Elem, t: Tree<Elem>): Tree<Elem>;
function containstree(x: Elem, xs: Tree<Elem>): bool;

function insert(x: Elem, t: Tree<Elem>): Tree<Elem>;

axiom
  length(nil) == 0;
axiom forall x: Elem, xs: Lst<Elem> ::
  length(cons(x,xs)) == length(xs) + 1;

axiom forall f: [Elem]Elem ::
  map(f, nil) == nil;
axiom forall f: [Elem]Elem, y: Elem, ys: Lst<Elem> ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

axiom forall ys: Lst<Elem> ::
  append(nil, ys) == ys;
axiom forall x: Elem, xs: Lst<Elem>, ys: Lst<Elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall x: Elem ::
  contains(x, nil) == false;
axiom forall x: Elem, y: Elem, ys: Lst<Elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom
  size(leaf) == 0;
axiom forall v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  size(node(v, l, r)) == size(l) + size(r) + 1;

axiom
  mirror(leaf) == leaf;
axiom forall v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  mirror(node(v, l, r)) == node(v, r, l);

axiom forall f: [Elem]Elem ::
  maptree(f, leaf) == leaf;
axiom forall f: [Elem]Elem, v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  maptree(f, node(v, l, r)) == node(f[v], maptree(f, l), maptree(f, r));

axiom
  elems(leaf) == nil;
axiom forall v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  elems(node(v, l, r)) == cons(v, append(elems(l), elems(r)));
  
axiom forall x: Elem ::
  containstree(x, leaf) == false;
axiom forall x: Elem, v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  containstree(x, node(v, l, r)) == (x == v || containstree(x, l) || containstree(x, r));

axiom forall x: Elem ::
  insert(x, leaf) == node(x, leaf, leaf);
axiom forall x: Elem, v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  insert(x, node(v, l, r)) == node(v, insert(x, l), r);
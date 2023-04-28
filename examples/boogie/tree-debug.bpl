type Elem;

data Tree<a> = leaf | node(value: a, left: Tree<a>, right: Tree<a>);

function containstree(x: Elem, xs: Tree<Elem>): bool;

function insert(x: Elem, t: Tree<Elem>): Tree<Elem>;

axiom forall x: Elem ::
  containstree(x, leaf) == false;
axiom forall x: Elem, v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  containstree(x, node(v, l, r)) == (x == v || containstree(x, l) || containstree(x, r));

axiom forall x: Elem ::
  insert(x, leaf) == node(x, leaf, leaf);
axiom forall x: Elem, v: Elem, l: Tree<Elem>, r: Tree<Elem> ::
  insert(x, node(v, l, r)) == node(v, insert(x, l), r);
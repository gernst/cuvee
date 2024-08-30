data Tree<a> = leaf | node(value: a, left: Tree<a>, right: Tree<a>);

function containstreeAll(x: int, xs: Tree<int>): bool;
function containstreeSort(x: int, xs: Tree<int>): bool;

axiom forall x: int ::
  containstreeAll(x, leaf) == false;
axiom forall x: int, v: int, l: Tree<int>, r: Tree<int> ::
  containstreeAll(x, node(v, l, r))
    == (x == v || containstreeAll(x, l) || containstreeAll(x, r));

axiom forall x: int ::
  containstreeSort(x, leaf) == false;
axiom forall x: int, v: int, l: Tree<int>, r: Tree<int> ::
  containstreeSort(x, node(v, l, r))
    == (x == v || x < v && containstreeSort(x,l) || x > v && containstreeSort(x,r));

type elem;
data list<a> = nil  | cons(head: a, tail: list<a>);
data tree<a> = leaf | node(value: a, left: tree<a>, right: tree<a>);

function length(xs: list<elem>): int;
function contains(x: elem, xs: list<elem>): bool;
function remove(x: elem, xs: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function size(xs: tree<elem>): int;
function elems(t: tree<elem>): list<elem>;

axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall x: elem ::
  remove(x, nil) == nil;
axiom forall x: elem, y: elem, ys: list<elem> ::
  remove(x, cons(y, ys)) == ite(x == y, remove(x, ys), cons(y, remove(x, ys)));

axiom forall x: elem ::
  contains(x, nil) == false;
axiom forall x: elem, y: elem, ys: list<elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom
  size(leaf) == 0;
axiom forall v: elem, l: tree<elem>, r: tree<elem> ::
  size(node(v, l, r)) == size(l) + size(r) + 1;

axiom
  elems(leaf) == nil;
axiom forall v: elem, l: tree<elem>, r: tree<elem> ::
  elems(node(v, l, r)) == cons(v, append(elems(l), elems(r)));
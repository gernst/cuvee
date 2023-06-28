type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function contains(x: elem, xs: list<elem>): bool;
function remove(x: elem, xs: list<elem>): list<elem>;
function count(x: elem, xs: list<elem>): int;

lemma forall n: int ::
  n - 0 == n;

axiom forall x: elem ::
  contains(x, nil) == false;
axiom forall x: elem, y: elem, ys: list<elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom forall x: elem ::
  remove(x, nil) == nil;
axiom forall x: elem, y: elem, ys: list<elem> ::
  remove(x, cons(y, ys)) == ite(x == y, remove(x, ys), cons(y, remove(x, ys)));

axiom forall x: elem ::
  count(x, nil) == 0;
axiom forall x: elem, y: elem, ys: list<elem> ::
  count(x, cons(y, ys)) == ite(x == y, count(x, ys) + 1, count(x, ys));
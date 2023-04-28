type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

// Declarations of functions

function sum(xs: list<int>): int;
function append(xs: list<int>, ys: list<int>): list<int>;

axiom
  sum(nil) == 0;
axiom forall x: int, xs: list<int> ::
  sum(cons(x,xs)) == sum(xs) + x;

axiom forall ys: list<int> ::
  append(nil, ys) == ys;
axiom forall x: int, xs: list<int>, ys: list<int> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));
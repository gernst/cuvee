type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function append(xs: list<elem>, ys: list<elem>): list<elem>;

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));
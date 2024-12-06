type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function append(xs: list<elem>, ys: list<elem>): list<elem>;

axiom forall ys: list<elem> ::
  append(nil, ys)
    == ys;

axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys)
    == cons(x, append(xs, ys));

function eq_append(xs: list<elem>, ys: list<elem>, zs: list<elem>): bool;

axiom forall ys: list<elem>, zs: list<elem> ::
  eq_append(nil, ys, zs) == (ys == zs);

axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  eq_append(cons(x, xs), ys, nil) == false;

axiom forall x: elem, xs: list<elem>, ys: list<elem>, z: elem, zs: list<elem> ::
  eq_append(cons(x, xs), ys, cons(z, zs)) == (x == z && eq_append(xs, ys, zs));

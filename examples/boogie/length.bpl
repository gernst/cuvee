type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function length(xs: list<elem>): int;
function nlength(xs: list<elem>, u: int): int;
function append(xs: list<elem>, ys: list<elem>): list<elem>;

axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;

axiom forall u: int ::
  nlength(nil, u) == u;
axiom forall x: elem, xs: list<elem>, u: int ::
  nlength(cons(x,xs), u) == nlength(xs, u) + 1;

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));
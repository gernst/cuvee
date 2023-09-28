type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function map (f: [elem]elem, xs: list<elem>): list<elem>;

axiom forall f: [elem]elem ::
  map(f, nil) == nil;
axiom forall f: [elem]elem, y: elem, ys: list<elem> ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

const g: [elem]elem;
function f(xs: list<elem>): list<elem> { map(g, xs) }
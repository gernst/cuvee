type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function append(xs: list<elem>, ys: list<elem>): list<elem>;
function butlast(xs: list<elem>): list<elem>;

// append
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

// butlast
axiom
  butlast(nil) == nil;
axiom forall x: elem, xs: list<elem> ::
  butlast(cons(x, xs)) == ite(xs == nil, nil, cons(x, butlast(xs)));

lemma forall x: elem, xs: list<elem> ::
  butlast(append(xs, cons(x, nil))) == xs
proof induction xs;
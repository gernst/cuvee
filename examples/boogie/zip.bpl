type elem;
data list<a> = nil | cons(head: a, tail: list<a>);
data pair<a,b> = pair(fst: a, snd: b);

function length(xs: list<elem>): int;
function append(xs: list<elem>, ys: list<elem>): list<elem>;
function zip(xs: list<elem>, ys: list<elem>): list<pair<elem,elem>>;

axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall ys: list<elem> ::
  zip(nil, ys) == nil;
axiom forall x: elem, xs: list<elem> ::
  zip(cons(x, xs), nil) == nil;
axiom forall x: elem, xs: list<elem>, y: elem, ys: list<elem> ::
  zip(cons(x, xs), cons(y, ys)) == cons(pair(x,y), zip(xs, ys));
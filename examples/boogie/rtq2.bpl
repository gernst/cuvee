type elem;
data option<a> = none | some(get: a);
data list<a>   = nil | cons(head: a, tail: list<a>);

function append(xs: list<elem>, ys: list<elem>): list<elem>;
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function snoc(xs: list<elem>, y: elem): list<elem>;
axiom forall z: elem ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: elem, y: elem, ys: list<elem> ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

function reverse(xs: list<elem>): list<elem>;
axiom
  reverse(nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  reverse(cons(y, ys)) == append(reverse(ys), cons(y, nil));

function hd(xs: list<elem>): option<elem>;
axiom
    hd(nil) == none;
axiom forall x: elem, xs: list<elem> ::
    hd(cons(x, xs)) == some(x);

function tl(xs: list<elem>): list<elem>;
axiom
    tl(nil) == nil;
axiom forall x: elem, xs: list<elem>::
    tl(cons(x, xs)) == xs;

data queue<a>
  = empty
  | part(hd1: a, tl1: list<a>)
  | full(hd2: a, tl2: list<a>, rs3: list<a>, ls3: a);

function abs(q: queue<elem>): list<elem>;
axiom
  abs(empty) == nil;
axiom forall x: elem, xs: list<elem> ::
  abs(part(x, xs)) == cons(x, xs);
axiom forall x: elem, xs: list<elem>, ys: list<elem>, y: elem ::
  abs(full(x, xs, ys, y)) == cons(x, append(xs, reverse(cons(y, ys))));

function push(q: queue<elem>, z: elem): queue<elem>;
axiom forall z: elem ::
  push(empty, z) == part(z, nil);
axiom forall z: elem, x: elem, xs: list<elem> ::
  push(part(x, xs), z) == full(x, xs, nil, z);
axiom forall z: elem, x: elem, xs: list<elem>, ys: list<elem>, y: elem ::
  push(full(x, xs, ys, y), z) == full(x, xs, cons(y, ys), z);

function peek(q: queue<elem>): option<elem>;
axiom
  peek(empty) == none;
axiom forall x: elem, xs: list<elem> ::
  peek(part(x, xs)) == some(x);
axiom forall x: elem, xs: list<elem>, ys: list<elem>, y: elem ::
  peek(full(x, xs, ys, y)) == some(x);

function pop(q: queue<elem>): queue<elem>;
axiom
  pop(empty) == empty;
axiom forall x: elem ::
  pop(part(x, nil)) == empty;
axiom forall x: elem, y: elem, ys: list<elem> ::
  pop(part(x, cons(y, ys))) == part(y, ys);
axiom forall x: elem, ys: list<elem>, y: elem ::
  pop(full(x, nil, ys, y)) == part(y, reverse(ys));
axiom forall x: elem, z: elem, xs: list<elem>, ys: list<elem>, y: elem ::
  pop(full(x, cons(z, xs), ys, y)) == full(z, xs, ys, y);
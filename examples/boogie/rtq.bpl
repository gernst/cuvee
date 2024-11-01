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

data queue<a> = queue(front: list<a>, back: list<a>);

function abs(q: queue<elem>): list<elem>;
axiom forall xs: list<elem>, ys: list<elem> ::
  abs(queue(xs, ys)) == append(xs, reverse(ys));

function abs_(q: queue<elem>): list<elem>;
axiom forall ys: list<elem> ::
  abs_(queue(nil, nil)) == nil;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  abs_(queue(cons(x,xs), ys)) == cons(x, append(xs, reverse(ys)));

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

function peek(q: queue<elem>): option<elem>;
axiom forall ys: list<elem> ::
    peek(queue(nil, nil)) == none;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
    peek(queue(cons(x, xs), ys)) == some(x);

function pop(q: queue<elem>): queue<elem>;
axiom
    pop(queue(nil, nil)) == queue(nil, nil);
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
    pop(queue(cons(x, nil), ys)) == queue(reverse(ys), nil);
axiom forall x: elem, y: elem, xs: list<elem>, ys: list<elem> ::
    pop(queue(cons(x, cons(y, xs)), ys)) == queue(cons(y, xs), ys);

function push(x: elem, q: queue<elem>): queue<elem>;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
    push(x, queue(xs, ys)) == queue(xs, cons(x, ys));

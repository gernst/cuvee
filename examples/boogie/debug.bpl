type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function snoc(xs: list<elem>, x: elem): list<elem>;
function filter(p: [elem]bool, xs: list<elem>): list<elem>;


axiom forall z: elem ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: elem, y: elem, ys: list<elem> ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

axiom forall p: [elem]bool ::
  filter(p, nil) == nil;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  filter(p, cons(y, ys)) == ite(p[y], cons(y, filter(p, ys)), filter(p, ys));
type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function all(p: [elem]bool, xs: list<elem>): bool;
function ex(p: [elem]bool, xs: list<elem>): bool;
function contains(x: elem, xs: list<elem>): bool;
function filter(p: [elem]bool, xs: list<elem>): list<elem>;

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

axiom forall p: [elem]bool ::
  all(p, nil) == true;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  all(p, cons(y, ys)) == (p[y] && all(p, ys));

axiom forall p: [elem]bool ::
  ex(p, nil) == false;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  ex(p, cons(y, ys)) == (p[y] || ex(p, ys));

axiom forall x: elem ::
  contains(x, nil) == false;
axiom forall x: elem, y: elem, ys: list<elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

axiom forall p: [elem]bool ::
  filter(p, nil) == nil;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  filter(p, cons(y, ys)) == ite(p[y], cons(y, filter(p, ys)), filter(p, ys));

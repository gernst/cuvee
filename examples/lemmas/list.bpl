type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

// Declarations of functions

function length(xs: list<elem>): int;
function qlength(xs: list<elem>, n: int): int;
function nlength(xs: list<elem>, n: int): int;
function map (f: [elem]elem, xs: list<elem>): list<elem>;
function all(p: [elem]bool, xs: list<elem>): bool;
function ex(p: [elem]bool, xs: list<elem>): bool;
function contains(x: elem, xs: list<elem>): bool;
function count(x: elem, xs: list<elem>): int;
function snoc(xs: list<elem>, x: elem): list<elem>;
function rotate(cnt: int, xs: list<elem>): list<elem>;
function take(cnt: int, xs: list<elem>): list<elem>;
function drop(cnt: int, xs: list<elem>): list<elem>;
function take_(cnt: int, xs: list<elem>): list<elem>;
function drop_(cnt: int, xs: list<elem>): list<elem>;
function reverse(xs: list<elem>): list<elem>;
function qreverse(xs: list<elem>, ys: list<elem>): list<elem>;
function nreverse(xs: list<elem>, ys: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;
function remove(x: elem, xs: list<elem>): list<elem>;
function filter(p: [elem]bool, xs: list<elem>): list<elem>;

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

// Axioms describing the functions declared above

// length
axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;

// qlength
axiom forall n: int ::
  qlength(nil, n) == n;
axiom forall x: elem, xs: list<elem>, n: int ::
  qlength(cons(x,xs), n) == qlength(xs, n + 1);

// nlength
axiom forall n: int ::
  nlength(nil, n) == n;
axiom forall x: elem, xs: list<elem>, n: int ::
  nlength(cons(x,xs), n) == nlength(xs, n) + 1;

// map
axiom forall f: [elem]elem ::
  map(f, nil) == nil;
axiom forall f: [elem]elem, y: elem, ys: list<elem> ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

// all
axiom forall p: [elem]bool ::
  all(p, nil) == true;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  all(p, cons(y, ys)) == (p[y] && all(p, ys));

// ex
axiom forall p: [elem]bool ::
  ex(p, nil) == false;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  ex(p, cons(y, ys)) == (p[y] || ex(p, ys));

// contains
axiom forall x: elem ::
  contains(x, nil) == false;
axiom forall x: elem, y: elem, ys: list<elem> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

// count
axiom forall x: elem ::
  count(x, nil) == 0;
axiom forall x: elem, y: elem, ys: list<elem> ::
  count(x, cons(y, ys)) == ite(x == y, count(x, ys) + 1, count(x, ys));

// snoc
axiom forall z: elem ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: elem, y: elem, ys: list<elem> ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

// rotate
axiom forall n: int ::
  rotate(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  rotate(n, cons(y, ys)) == ite(n <= 0, cons(y, ys), snoc(rotate(n-1, ys), y));

// take
axiom forall n: int ::
  take(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  take(n, cons(y, ys)) == ite(n <= 0, nil, cons(y, take(n - 1, ys)));

// take_
axiom forall n: int ::
  take_(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  take_(0, cons(y, ys)) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  take_(n + 1, cons(y, ys)) == cons(y, take_(n , ys));

// drop
axiom forall n: int ::
  drop(n, nil) == nil;
axiom forall n: int, y: elem, ys: list<elem> ::
  drop(n, cons(y, ys)) == ite(n <= 0, cons(y, ys), drop(n - 1, ys));

// drop_
axiom forall n: int ::
  drop_(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  drop_(0, cons(y, ys)) == cons(y, ys);
axiom forall n: int, y: elem, ys: list<elem> ::
  drop_(n + 1, cons(y, ys)) == drop_(n , ys);

// reverse
axiom
  reverse(nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  reverse(cons(y, ys)) == snoc(reverse(ys), y);

// qreverse
axiom forall zs: list<elem> ::
  qreverse(nil, zs) == zs;
axiom forall zs: list<elem>, y: elem, ys: list<elem> ::
  qreverse(cons(y, ys), zs) == qreverse(ys, cons(y, zs));

// nreverse
axiom forall zs: list<elem> ::
  nreverse(nil, zs) == zs;
axiom forall zs: list<elem>, y: elem, ys: list<elem> ::
  nreverse(cons(y, ys), zs) == snoc(nreverse(ys, zs), y);

// append
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

// remove
axiom forall x: elem ::
  remove(x, nil) == nil;
axiom forall x: elem, y: elem, ys: list<elem> ::
  remove(x, cons(y, ys)) == ite(x == y, remove(x, ys), cons(y, remove(x, ys)));

// filter
axiom forall p: [elem]bool ::
  filter(p, nil) == nil;
axiom forall p: [elem]bool, y: elem, ys: list<elem> ::
  filter(p, cons(y, ys)) == ite(p[y], cons(y, filter(p, ys)), filter(p, ys));

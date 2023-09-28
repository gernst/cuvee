// Large collection of functions in the theory of lists,
// more specific benchmarks are in subfolder "list/",
// which incldudes some variants,
// such as tail-recursive or more generic versions of length or reverse.

// TheSy does not support anonymous sorts,
// so we formulate this theory over lists of natural numbers

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function map (f: [nat]nat, xs: list): list;
axiom forall f: [nat]nat ::
  map(f, nil) == nil;
axiom forall f: [nat]nat, y: nat, ys: list ::
  map(f, cons(y, ys)) == cons(f[y], map(f, ys));

function all(p: [nat]bool, xs: list): bool;
axiom forall p: [nat]bool ::
  all(p, nil) == true;
axiom forall p: [nat]bool, y: nat, ys: list ::
  all(p, cons(y, ys)) == (p[y] && all(p, ys));

function ex(p: [nat]bool, xs: list): bool;
axiom forall p: [nat]bool ::
  ex(p, nil) == false;
axiom forall p: [nat]bool, y: nat, ys: list ::
  ex(p, cons(y, ys)) == (p[y] || ex(p, ys));

function contains(x: nat, xs: list): bool;
axiom forall x: nat ::
  contains(x, nil) == false;
axiom forall x: nat, y: nat, ys: list ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));


function count(x: nat, xs: list): nat;
axiom forall x: nat ::
  count(x, nil) == zero;
axiom forall x: nat, y: nat, ys: list ::
  count(x, cons(y, ys)) == if x == y then succ(count(x, ys)) else count(x, ys);

function snoc(xs: list, x: nat): list;
axiom forall z: nat ::
  snoc(nil, z) == cons(z, nil);
axiom forall z: nat, y: nat, ys: list ::
  snoc(cons(y, ys), z) == cons(y, snoc(ys, z));

function rotate(cnt: nat, xs: list): list;
axiom forall n: nat ::
  rotate(n, nil) == nil;
axiom forall y: nat, ys: list ::
  rotate(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: nat, ys: list ::
  rotate(succ(n), cons(y, ys)) == snoc(rotate(n-1, ys), y);

function take(cnt: nat, xs: list): list;
axiom forall n: nat ::
  take(n, nil) == nil;
axiom forall y: nat, ys: list ::
  take(zero, cons(y, ys)) == nil;
axiom forall n: nat, y: nat, ys: list ::
  take(succ(n), cons(y, ys)) == cons(y, take(n , ys));

function drop(cnt: nat, xs: list): list;
axiom forall n: nat ::
  drop(n, nil) == nil;
axiom forall y: nat, ys: list ::
  drop(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: nat, ys: list ::
  drop(succ(n), cons(y, ys)) == drop(n , ys);

function reverse(xs: list): list;
axiom
  reverse(nil) == nil;
axiom forall y: nat, ys: list ::
  reverse(cons(y, ys)) == snoc(reverse(ys), y);

function remove(x: nat, xs: list): list;
axiom forall x: nat ::
  remove(x, nil) == nil;
axiom forall x: nat, y: nat, ys: list ::
  remove(x, cons(y, ys)) == ite(x == y, remove(x, ys), cons(y, remove(x, ys)));

function filter(p: [nat]bool, xs: list): list;
axiom forall p: [nat]bool ::
  filter(p, nil) == nil;
axiom forall p: [nat]bool, y: nat, ys: list ::
  filter(p, cons(y, ys)) == ite(p[y], cons(y, filter(p, ys)), filter(p, ys));

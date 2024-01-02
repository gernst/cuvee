data nat = zero | succ(pred: nat);

data pair<a,b> = pair(fst: a, snd: b);

type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function add(m: nat, n: nat): nat;
function mul(m: nat, n: nat): nat;

axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

axiom forall n: nat ::
  mul(zero, n) == zero;
axiom forall m: nat, n: nat ::
  mul(succ(m), n) == add(n, mul(m, n));

function append(xs: list<elem>, ys: list<elem>): list<elem>;
axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


function append_(xs: list<pair<elem, nat>>, ys: list<pair<elem, nat>>): list<pair<elem, nat>>;
axiom forall ys: list<pair<elem, nat>> ::
  append_(nil, ys) == ys;
axiom forall x: pair<elem, nat>, xs: list<pair<elem, nat>>, ys: list<pair<elem, nat>> ::
  append_(cons(x,xs), ys) == cons(x, append_(xs, ys));

function replicate(a: elem, n: nat): list<elem>;
axiom forall a: elem ::
  replicate(a, zero) == nil;
axiom forall a: elem, n: nat::
  replicate(a, succ(n)) == cons(a, replicate(a, n));

function expand(xs: list<pair<elem, nat>>): list<elem>;
axiom
  expand(nil) == nil;
axiom forall a: elem, n: nat, xs: list<pair<elem, nat>> ::
  expand(cons(pair(a, n), xs)) == append(replicate(a, n), expand(xs));

function cons_c(p: pair<elem, nat>, xs: list<pair<elem, nat>>): list<pair<elem, nat>>;
// this axiom works better for expand:1:cons_c
// axiom  forall a: elem, n: nat ::
//   cons_c(pair(a, n), nil) == cons(pair(a, n), nil);

// this axiom works better wenn comparing (?)
// axiom  forall p: pair<elem, nat> ::
//  cons_c(p, nil) == cons(p, nil);
axiom  forall a: elem, n: nat, b: elem, m : nat, xs: list<pair<elem, nat>> ::
  cons_c(pair(a, n), cons(pair(b, m), xs))
      == if a == b then cons(pair(a, add(n, m)), xs)
                   else cons(pair(a, n), cons(pair(b, m), xs));


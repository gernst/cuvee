type char;

data nat
  = zero | succ(pred: nat);

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

function sub(m: nat, n: nat): nat;
axiom forall m: nat ::
  sub(m, zero) == m;
axiom forall n: nat ::
  sub(zero, n) == zero;
axiom forall m: nat, n: nat ::
  sub(succ(m), succ(n)) == sub(m,n);

function leq(m: nat, n: nat): bool;
axiom forall n: nat ::
  leq(zero, n) == true;
axiom forall m: nat ::
  leq(succ(m), zero) == false;
axiom forall m: nat, n: nat ::
  leq(succ(m), succ(n)) == leq(m, n);

data string
  = nil
  | cons(head: char, tail: string);

data rope
  = leaf(text: string)
  | node(weight: nat, left: rope, right: rope);


function string_length(xs: string): nat;
axiom
  string_length(nil)
    == zero;
axiom forall x: char, xs: string ::
  string_length(cons(x,xs))
    == succ(string_length(xs));

function string_concat(xs: string, ys: string): string;
axiom forall ys: string ::
  string_concat(nil, ys)
    == ys;
axiom forall x: char, xs: string, ys: string ::
  string_concat(cons(x,xs), ys)
    == cons(x, string_concat(xs, ys));


function string_take(cnt: nat, xs: string): string;
axiom forall n: nat ::
  string_take(n, nil)
    == nil;
axiom forall ys: string ::
  string_take(zero, ys)
    == nil;
axiom forall n: nat, y: char, ys: string ::
  string_take(succ(n), cons(y, ys))
    == cons(y, string_take(n, ys));

function repr(r: rope): string;
axiom forall text: string ::
  repr(leaf(text))
    == text;
axiom forall weight: nat, left: rope, right: rope ::
  repr(node(weight, left, right))
    == string_concat(repr(left), repr(right));

function rope_length(r: rope): nat;
axiom forall text: string ::
    rope_length(leaf(text))
      == string_length(text);
axiom forall weight: nat, left: rope, right: rope ::
    rope_length(node(weight, left, right))
      == add(weight, rope_length(right));

function rope_concat(r: rope, s: rope): rope;
axiom forall r: rope, s: rope ::
  rope_concat(r, s)
    == node(rope_length(r), r, s);

function rope_take2(n: nat, r: rope): rope;
axiom forall t: string, n: nat ::
  rope_take2(n, leaf(t))
    == leaf (string_take(n,t));
axiom forall weight: nat, left: rope, right: rope, n: nat ::
  rope_take2(n, node(weight, left, right)) 
    == rope_concat(rope_take2(n, left), rope_take2(sub(n,weight),right));

function repr_rope_take2(n: nat, r: rope): string;
axiom forall n: nat, t: string ::
  repr_rope_take2(n, leaf(t))
    == string_take(n, t);
axiom forall n: nat, weight: nat, left: rope, right: rope ::
  repr_rope_take2(n, node(weight, left, right))
    == string_concat(repr_rope_take2(n, left), repr_rope_take2(sub(n, weight), right));

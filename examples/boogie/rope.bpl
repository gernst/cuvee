type char;

data nat
    = zero | succ(pred: nat);

function add(m: nat, n: nat): nat;
axiom forall n: nat ::
  add(zero, n) == n;
axiom forall m: nat, n: nat ::
  add(succ(m), n) == succ(add(m, n));

data string
    = nil | cons(head: char, tail: string);

function string_length(xs: string): nat;
axiom
  string_length(nil) == zero;
axiom forall x: char, xs: string ::
  string_length(cons(x,xs)) == succ(string_length(xs));

function string_concat(xs: string, ys: string): string;
axiom forall ys: string ::
  string_concat(nil, ys) == ys;
axiom forall x: char, xs: string, ys: string ::
  string_concat(cons(x,xs), ys) == cons(x, string_concat(xs, ys));

data rope
    = leaf(text: string)
    | node(weight: nat, left: rope, right: rope);

function repr(r: rope): string;
axiom forall text: string ::
    repr(leaf(text)) == text;
axiom forall weight: nat, left: rope, right: rope ::
    repr(node(weight, left, right)) == string_concat(repr(left), repr(right));

function rope_length(r: rope): nat;
axiom forall text: string ::
    rope_length(leaf(text)) == string_length(text);
axiom forall weight: nat, left: rope, right: rope ::
    rope_length(node(weight, left, right)) == add(weight, rope_length(right));

function rope_concat(r: rope, s: rope): rope;
axiom forall r: rope, s: rope ::
  rope_concat(r, s) == node(rope_length(r), r, s);

lemma forall s: string, r: rope ::
  s == repr(r) <==> (string_concat(repr(left(r)), repr(right(r))) == s || text(r) == nil)
proof induction s{
  case nil => auto
  case cons(c, s) => auto
};
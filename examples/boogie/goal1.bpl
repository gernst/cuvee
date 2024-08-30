data nat = zero | succ(pred: nat);

type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function take(n: nat, xs: list<elem>): list<elem>;
function drop(n: nat, xs: list<elem>): list<elem>;
function append(xs: list<elem>, ys: list<elem>): list<elem>;

axiom forall ys: list<elem> ::
  append(nil, ys) == ys;
axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

axiom forall n: nat ::
  take(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  take(zero, cons(y, ys)) == nil;
axiom forall n: nat, y: elem, ys: list<elem> ::
  take(succ(n), cons(y, ys)) == cons(y, take(n , ys));

axiom forall n: nat ::
  drop(n, nil) == nil;
axiom forall y: elem, ys: list<elem> ::
  drop(zero, cons(y, ys)) == cons(y, ys);
axiom forall n: nat, y: elem, ys: list<elem> ::
  drop(succ(n), cons(y, ys)) == drop(n , ys);

lemma forall n: nat, xs: list<elem> ::
  append(take(n, xs), drop(n, xs)) == xs
proof induction xs;
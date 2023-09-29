data regex
  = empty | epsilon
  | seq(first: regex, second: regex)
  | choice(left: regex, right: regex)
  ;

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function append(xs: list, ys: list): list;
axiom forall ys: list ::
  append(nil, ys) == ys;
axiom forall x: nat, xs: list, ys: list ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));


function nullable(r: regex): bool;

axiom
  nullable(empty) == false;

axiom
  nullable(epsilon) == true;

axiom forall w1: list, w2: list ::
  nullable(seq(w1, w2)) == (nullable(w1) && nullable(w2));

axiom forall w1: list, w2: list ::
  nullable(choice(w1, w2)) == (nullable(w1) || nullable(w2));


function derive(a: nat, r: regex): bool;

axiom forall a: nat ::
  derive(a, empty) == empty;

axiom forall a: nat ::
  derive(a, epsilon) == empty;

axiom forall a: nat, r1: regex, r2: regex ::
  derive(a, choice(r1, r2)) == choice(derive(a, r1), derive(a, r2));
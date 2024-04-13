data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

data regex
  = empty | epsilon
  | letter(sym: nat)
  | seq(first: regex, second: regex)
  | choice(left: regex, right: regex)
  ;


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

axiom forall a: nat ::
  nullable(letter(a)) == false;

axiom forall r1: regex, r2: regex ::
  nullable(seq(r1, r2)) == (nullable(r1) && nullable(r2));

axiom forall r1: regex, r2: regex ::
  nullable(choice(r1, r2)) == (nullable(r1) || nullable(r2));


function derive(a: nat, r: regex): regex;

axiom forall a: nat ::
  derive(a, empty) == empty;

axiom forall a: nat ::
  derive(a, epsilon) == empty;

axiom forall a: nat, b: nat ::
  derive(a, letter(b)) ==
    if a == b then epsilon
    else empty;

axiom forall a: nat, r1: regex, r2: regex ::
  derive(a, choice(r1, r2)) == choice(derive(a, r1), derive(a, r2));

axiom forall a: nat, r1: regex, r2: regex ::
  derive(a, seq(r1, r2)) == 
    if nullable(r1)
    then choice(derive(a, r2), seq(derive(a, r1), r2))
    else seq(derive(a, r1), r2);
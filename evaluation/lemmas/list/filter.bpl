// characteristic lemmas
//   result of filtering/counting under all/none preconditions
//   length(filter(p, xs)) == countif(p, xs)

data nat = zero | succ(pred: nat);
data list = nil | cons(head: nat, tail: list);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true)  == false;

function length(xs: list): nat;
axiom
  length(nil) == zero;
axiom forall x: nat, xs: list ::
  length(cons(x,xs)) == succ(length(xs));

function filter(p: [nat]bool, xs: list): list;
axiom forall p: [nat]bool ::
  filter(p, nil) == nil;
axiom forall p: [nat]bool, y: nat, ys: list ::
  filter(p, cons(y, ys)) == if p[y] then cons(y, filter(p, ys)) else filter(p, ys);

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

function countif(p: [nat]bool, xs: list): nat;
axiom forall p: [nat]bool ::
  countif(p, nil) == zero;
axiom forall p: [nat]bool, y: nat, ys: list ::
  countif(p, cons(y, ys)) == if p[y] then succ(countif(p, ys)) else countif(p, ys);
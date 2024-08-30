data list<a> = nil | cons(head: a, tail: list<a>);

function not_(b: bool): bool;
axiom not_(false) == true;
axiom not_(true) == false;

function append(xs: list<int>, ys: list<int>): list<int>;
axiom forall ys: list<int> ::
  append(nil, ys) == ys;
axiom forall x: int, xs: list<int>, ys: list<int> ::
  append(cons(x,xs), ys) == cons(x, append(xs, ys));

function insort(x: int, xs: list<int>): list<int>;
axiom forall x: int ::
  insort(x, nil) == cons(x, nil);
axiom forall x: int, y: int, ys: list<int> ::
  insort(x, cons(y, ys)) ==
    if x == y then cons(y, ys)
    else if x < y then cons(x, cons(y, ys))
    else cons(y, insort(x, ys));

function length(xs: list<int>): int;
axiom
  length(nil) == 0;
axiom forall x: int, xs: list<int> ::
  length(cons(x,xs)) == length(xs) + 1;

function contains(x: int, xs: list<int>): bool;
axiom forall x: int ::
  contains(x, nil) == false;
axiom forall x: int, y: int, ys: list<int> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));
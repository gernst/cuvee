data list<a> = nil | cons(head: a, tail: list<a>);

function contains(x: int, xs: list<int>): bool;

axiom forall x: int ::
  contains(x, nil) == false;
axiom forall x: int, y: int, ys: list<int> ::
  contains(x, cons(y, ys)) == (x == y || contains(x, ys));

function sorted(xs: list<int>): bool;

axiom
    sorted(nil) == true;
axiom forall x: int, xs: list<int> ::
    sorted(cons(x, xs)) ==
      (forall y: int :: contains(y, xs) ==> x <= y) && sorted(xs);

function merge(xs: list<int>, ys: list<int>): list<int>;

axiom forall ys: list<int> ::
    merge(nil, ys) == ys;
axiom forall xs: list<int> ::
    merge(xs, nil) == xs;
axiom forall x: int, xs: list<int>, y: int, ys: list<int> ::
    merge(cons(x, xs), cons(y, ys))
        == if x < y then cons(x, merge(xs, cons(y, ys)))
                    else cons(y, merge(cons(x, xs), ys));

lemma forall z: int, xs: list<int>, ys: list<int> ::
    contains(z, merge(xs, ys)) == (contains(z, xs) || contains(z, ys))
proof
  induction xs {
    case nil =>
      auto
    case cons(x, xs) =>
      induction ys{
        case nil => auto
        case cons(y, ys) => auto
      }
  };

// what's the needed lemma?
goal forall xs: list<int>, ys: list<int> :: sorted(xs) && sorted(ys) ==> sorted(merge(xs, ys))
proof
  induction xs {
    case nil => auto
    case cons(x, xs) => auto
  };

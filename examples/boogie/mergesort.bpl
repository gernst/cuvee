data list<a> = nil | cons(head: a, tail: list<a>);

function sorted(xs: list<int>): bool;

axiom
    sorted(nil) == true;
axiom forall x: int ::
    sorted(cons(x, nil)) == true;
axiom forall x: int, y: int, zs: list<int> ::
    sorted(cons(x, cons(y, zs))) == (x < y && sorted(cons(y, zs)));

function merge(xs: list<int>, ys: list<int>): list<int>;

axiom forall ys: list<int> ::
    merge(nil, ys) == ys;
axiom forall xs: list<int> ::
    merge(xs, nil) == xs;
axiom forall x: int, xs: list<int>, y: int, ys: list<int> ::
    merge(cons(x, xs), cons(y, ys))
        == if x < y then cons(x, merge(xs, cons(y, ys)))
                    else cons(y, merge(cons(x, xs), ys));

// what's the needed lemma?
// try phone book with speculative generalization

// use predicate abstraction from the first unfolding of a recursive predicate,
// then find out *which* values satisfy the exposed conditions (may even compute)
// do it forward for left-fold, and backward for right-fold

// try quicksort pivot and bubblesort

// find way to do aggregates in this framework easily and without instrumentation

type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function isdigit(x: elem): bool;

function tolist(a: [int]elem, i: int, n: int): list<elem>;
axiom forall n: int, a: [int]elem ::
    tolist(a, n, n) == nil;
axiom forall i: int, n: int, a: [int]elem ::
    i < n ==> tolist(a, i, n) == cons(a[i], tolist(a, i+1, n));

function filter(xs: list<elem>): list<elem>;
axiom filter(nil) == nil;
axiom forall x: elem, xs: list<elem> ::
     isdigit(x) ==> filter(cons(x,xs)) == cons(x, filter(xs));
axiom forall x: elem, xs: list<elem> ::
    !isdigit(x) ==> filter(cons(x,xs)) == filter(xs);

procedure compare(a: [int]elem, m: int, b: [int]elem, n: int)
    returns (r: bool)
    requires 0 <= m && 0 <= n;
    ensures  r <==> filter(tolist(a, 0, m)) == filter(tolist(b, 0, n));
{
    r := false;
    var i: int, j: int := 0, 0;

    while(true)
        decreases (m + n) - (i + j);
        invariant 0 <= i && i <= m
               && 0 <= j && j <= n;
        summary   r <==> filter(tolist(a, old(i), m)) == filter(tolist(b, old(j), n));
    {
        if(i == m && j == n)              { r := true; break; }
        else if (i < m && !isdigit(a[i])) { i := i + 1; }
        else if (j < n && !isdigit(b[j])) { j := j + 1; }
        else if (i < m && j < n && a[i] == b[j]) { i := i + 1; j := j + 1; }
        else                              { r := false; break; }
    }
}
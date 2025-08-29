type Trace<a>;

function current<a>(xs: Trace<a>): a;
function earlier<a>(k: int, xs: Trace<a>): a;

function counter(n: int): Trace<int>;
function range(start: int, step: int, n: int): Trace<int>;

function consts<a>(value: a, n: int): Trace<int>;
function stores<a,b>(init: [a]b, keys: Trace<a>, values: Trace<b>): Trace<[a]b>;
function sums<a>(array: [a]int, keys: Trace<a>): Trace<int>;


// general rules that can only be implemented in the simplifier,
// which is not done yet:
// - normalize current(map(y <- ys, f)) to f(current(ys))
// - reduce invariants with earlier and universal quantifier
// - perhaps break down invariants at conjunctions (?)


free lemma {:rw} <a> forall value: a, n: int ::
    map(for k <- counter(n) yield value)
        == consts(value, n);

free lemma {:rw} forall start: int, step: int, n: int ::
    trace(start, for k <- counter(n) do i := step + i)
        == range(start, step, n);


free lemma {:rw} forall start: int, n: int ::
    range(0, 1, n) == counter(n);

free lemma {:rw} <a> forall value: a, n: int ::
    current(consts(value, n))
        == value;

free lemma {:rw} <a> forall value: a, j: int, n: int ::
    0 <= j && j < n
        ==> earlier(j, consts(value, n))
            == value;

free lemma {:rw} <a> forall value: a, j: int, n: int ::
    current(consts(value, n))
        == value;

free lemma {:rw} forall n: int ::
    current(counter(n))
        == n;

free lemma {:rw} forall start: int, step: int, n: int ::
    current(range(start, step, n))
        == start + step * n;

free lemma {:rw} forall k: int, n: int ::
    invariant(for i <- counter(k) yield i < n)
        <==> 0 <= k && k <= n;

free lemma {:rw} forall start: int, k: int, n: int ::
    invariant(for i <- range(start, 1, k) yield i < n)
        <==> 0 <= k && k <= n;

free lemma {:rw} forall start: int, k: int, n: int ::
    invariant(for i <- range(start, -1, k) yield n < i)
        <==> 0 <= k && k <= n;


free lemma {:rw} <a,b> forall init: [a]b, keys: Trace<a>, values: Trace<b> ::
    trace(init, for k, v <- keys, values do a := a[k:=v])
        == stores(init, keys, values);

free lemma {:rw} <b> forall init: [int]b, values: Trace<b>, j: int, n: int ::
    current(stores(init, counter(n), values))[j]
        == if 0 <= j && j < n then earlier(j, values) else init[j];
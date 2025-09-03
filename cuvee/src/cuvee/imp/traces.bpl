function counter(n: int): Trace<int>;

free lemma {:rw} forall n: int ::
    current(counter(n)) == n;

free lemma {:rw} forall k: int, n: int ::
    0 <= k && k < n
        ==> earlier(k, ⌊counter(n)⌋) == k;

free lemma {:rw} forall start: int, step: int, n: int ::
    trace(start, for k <- ⌊counter(n)⌋ do i := step + i)
        == map(for k <- counter(n) yield start + step * k);


free lemma {:rw} <a> forall m: int, n: int ::
    invariant(for k <- ⌊counter(n)⌋ yield k < m)
        <==> 0 <= n && n <= m;


function consts<a>(value: a, n: int): Trace<int>;

free lemma {:rw} <a> forall value: a, n: int ::
    map(for k <- ⌊counter(n)⌋ yield value)
        == ⌊consts(value, n)⌋;

free lemma {:rw} <a> forall value: a, n: int ::
    current(consts(value, n))
        == value;

free lemma {:rw} <a> forall value: a, k: int, n: int ::
    0 <= k && k < n
        ==> earlier(k, ⌊consts(value, n)⌋)
            == value;


function stores<a,b>(init: [a]b, keys: Trace<a>, values: Trace<b>): Trace<[a]b>;

free lemma {:rw} <a,b> forall init: [a]b, keys: Trace<a>, values: Trace<b> ::
    trace(init, for k, v <- keys, values do a := a[k:=v])
        == stores(init, keys, values);

free lemma {:rw} <b> forall init: [int]b, values: Trace<b>, j: int, n: int ::
    current(stores(init, ⌊counter(n)⌋, values))[j]
        == if 0 <= j && j < n then earlier(j, values) else init[j];

free lemma {:rw} <b> forall init: [int]b, values: Trace<b>, j: int, k: int, n: int ::
    0 <= k && k < n
        ==> earlier(k, stores(init, ⌊counter(n)⌋, values))[j]
            == if 0 <= j && j < k then earlier(j, values) else init[j];
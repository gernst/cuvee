type Trace<a>;

function counter(n: int): Trace<int>;

free lemma {:rw} forall n: int ::
    current(counter(n)) == n;

free lemma {:rw} forall k: int, n: int ::
    0 <= k && k < n
        ==> earlier(k, ⌊counter(n)⌋) == k;

free lemma {:rw} forall start: int, step: int, n: int ::
    trace(start, for k <- ⌊counter(n)⌋ do i := step + i)
        == map(for k <- counter(n) yield start + step * k);

free lemma {:rw} <a> forall n: int, values: Trace<a> ::
    map(for k <- ⌊counter(n)⌋ yield earlier(k, values))
        == values;

free lemma {:rw} <a> forall init: a, n: int, values: Trace<a> ::
    current(trace(init, for k, v <- ⌊counter(n)⌋, values do x := v))
        == if n == 0 then init else current(values);

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

free lemma {:rw} <b> forall init: [int]b, values: Trace<b>, j: int, start: int, n: int ::
    current(stores(init, map(for k <- ⌊counter(n)⌋ yield start + k), values))[j]
        == if start <= j && j < start + n then earlier(j, values) else init[j];

free lemma {:rw} <b> forall init: [int]b, values: Trace<b>, j: int, k: int, n: int ::
    0 <= k && k < n
        ==> earlier(k, stores(init, ⌊counter(n)⌋, values))[j]
            == if 0 <= j && j < k then earlier(j, values) else init[j];


function shift(a: [int]int, keys: Trace<int>, delta: int): Trace<[int]int>;

free lemma {:rw} <a,b> forall init: [a]b, keys: Trace<a>, delta: b ::
    trace(init, for k <- keys do a := a[k:=a[k + delta]])
        == shift(init, keys, delta);

free lemma {:rw} forall a: [int]int, n: int, delta: int, k: int ::
  0 <= delta ==>
    current(shift(a, ⌊counter(n)⌋, delta))[k]
      == if 0 <= k && k < n
         then a[k + delta]
         else a[k];


function sums(init: int, values: Trace<int>): Trace<int>;

free lemma {:rw} forall init: int, values: Trace<int> ::
    trace(init, for v <- values do s := s + v)
        == sums(init, values);

free lemma {:rw} forall init: int, values: Trace<int> ::
    trace(init, for v <- values do s := v + s)
        == sums(init, values);

free lemma {:rw} forall init: int, values: Trace<int> ::
    current(sums(0, map(for v <- values yield - v)))
        == - current(sums(0, values));

free lemma {:rw} forall init: int, values: Trace<int> ::
    current(sums(init, values))
        == init + current(sums(0, values));

function sum(init: int, values: Trace<int>): int;

free lemma {:rw} forall values: Trace<int> ::
     0 + current(sums(0, values))
        == sum(0, values);

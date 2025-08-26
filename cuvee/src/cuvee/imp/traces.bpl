type Trace<a>;

function current<a>(xs: Trace<a>): a;

function counter(n: int): Trace<int>;
function range(start: int, step: int, n: int): Trace<int>;

function selects<a,b>(init: [a]b, keys: Trace<a>): Trace<b>;
function stores<a,b>(init: [a]b, keys: Trace<a>, values: Trace<b>): Trace<[a]b>;

function holds<a>(xs: Trace<a>): bool;
function sums<a>(array: [a]int, keys: Trace<a>): Trace<int>;



free lemma {:rw} forall start: int, step: int, n: int ::
    trace(start, for k <- [ counter(n) ] do i := step + i)
        == range(start, step, n);


free lemma {:rw} forall start: int, n: int ::
    range(0, 1, n) == counter(n);


free lemma {:rw} forall n: int ::
    current(counter(n)) == n;

free lemma {:rw} forall start: int, step: int, n: int ::
    current(range(start, step, n)) == start + step * n;
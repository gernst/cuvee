type Trace<a>;
function earlier<a>(x: a, xs: Trace<a>): bool;
function current<a>(x: a, xs: Trace<a>): bool;

function range(start: int, step: int, stop: int): Trace<int>;

lemma forall i0: int, c: int, k: int, ks: Trace<int>, n: int ::
    trace(i0, for k <- [ ks ] do i := if (i < n) then (c + i))
        == range(i0, c, n);
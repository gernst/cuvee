type Trace<a>;
function earlier<a>(x: a, xs: Trace<a>): bool;
function current<a>(x: a, xs: Trace<a>): bool;

function range(start: int, step: int, stop: int): Trace<int>;

lemma forall i0: int, c: int, n: int ::
    trace(i0, for  <- [  ] do i := if (i < n) then (i + c))
        == range(i0, c, n);
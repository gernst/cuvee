type Trace<a>;
function current<a>(x: a, xs: Trace<a>): bool;
function range(start: int, step: int, stop: int): Trace<int>;

free lemma {:rw} forall i: int, i0: int, i1: int, n: int ::
    current(i, trace(i0, for k <- [ range(0, 1, n) ] do i := i1))
        <==> if n == 0 then i == i0 else i == i1;

goal forall j: int, n: int ::
    current(j, trace(0, for k <- [ range(0, 1, n) ] do i := 1));
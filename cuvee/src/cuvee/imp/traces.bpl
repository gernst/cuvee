type Trace<a>;
function earlier<a>(x: a, xs: Trace<a>): bool;
function current<a>(x: a, xs: Trace<a>): bool;

function range(start: int, step: int, stop: int): Trace<int>;
function update<a,b>(array: [a]b, as: Trace<a>, bs: Trace<b>): [a]b;

// dependency ks is dummy
lemma forall i0: int, c: int, k: int, ks: Trace<int>, n: int ::
    trace(i0, for k <- [ ks ] do i := if (i < n) then (c + i))
        == range(i0, c, n);

// so far, only have step of 1
lemma forall j: int, i: int, n: int ::
    current(j, range(i, 1, n))
        == i <= j && j <= n;

lemma {:rw} forall a0: [int]int, a: [int]int, ks: Trace<int>, vs: Trace<int> :: 
    current(a, trace(a0, for k, v <- [ ks, vs ] do a := a[k := v]))
        <==> a == update(a0, ks, vs);
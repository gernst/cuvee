const c: int;
function P(x: int): bool;
function Q(x: int, y: int): bool;

axiom forall z: int ::
  Q(c, z) == P(z);

goal forall x: int, y: int ::
    x != c || Q(x, y);

type Trace<a>;
function current<a>(x: a, xs: Trace<a>): bool;

function range(start: int, step: int, stop: int): Trace<int>;

lemma {:rw} forall i0: int, c: int, ks: Trace<int>, n: int ::
    trace(i0, for k <- [ ks ] do i := if i < n then i + c | if i < n then c + i)
        == range(i0, c, n);

goal forall m: int, ks: Trace<int> ::
    trace(0, for k <- [ ks ] do i := if (i < m) then i + 1 + 0)
        == range(0, 1, m);

goal forall m: int, is: Trace<int>, ks: Trace<int>, c: int ::
    is == trace(0, for k <- [ ks ] do i := if (i < m) then 3 + i)
        ==> is == range(0, c, m);

function update<a,b>(array: [a]b, as: Trace<a>, bs: Trace<b>): [a]b;

// This lemma gets rid of the trace form but still depends on sort Trace,
// which can be further refined by other lemmas.
// Note, matching a concrete array update against ks and vs
// will produce map terms that propagate dependencies into the argument of update.

lemma {:rw} forall a0: [int]int, a: [int]int, ks: Trace<int>, vs: Trace<int> :: 
    current(a, trace(a0, for k, v <- [ ks, vs ] do a := a[k := v]))
        <==> a == update(a0, ks, vs);

goal forall a0: [int]int, a: [int]int, as: Trace<[int]int>, i: int, v: int, n: int ::
       as == trace(a0, for i <- [ range(0, 1, n) ] do a := a[i := i + 1])
    && current(a, as)
        ==> a[i] == v;

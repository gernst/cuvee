
// from inclusive, to exclusive
function sum(a: [int]int, from: int, to: int, base: int, factor: int): int;

// base case
free lemma forall a:[int]int ::
    { sum(a, 0, 0, 0, 1) }
    sum(a, 0, 0, 0, 1) == 0;

// recursion
free lemma forall a: [int]int, to: int ::
    1 <= to ==> sum(a, 1, to, 0, 1) == sum(a, 0, to, 0, 1) - a[0];

free lemma forall a: [int]int, to: int ::
    0 <= to ==> sum(a, 0, to+1, 0, 1) == sum(a, 0, to, 0, 1) + a[to];

free lemma forall a: [int]int, i: int, n: int, z: int ::
    0 <= i && i < n ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1) - a[i] + z;

free lemma forall a: [int]int, i: int, n: int, z: int ::
    i < 0 && 0 <= n ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1);
  
free lemma forall a: [int]int, i: int, n: int, z: int ::
    0 <= n && n <= i ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1);

// from inclusive, to exclusive
function shift(a: [int]int, from: int, to: int, delta: int): [int]int;

free lemma forall a: [int]int, n: int, k: int ::
  shift(a, 0, n, 1)[k]
    == if 0 <= k && k < n
       then a[k + 1]
       else a[k];

free lemma forall a: [int]int, n: int ::
    { sum(shift(a, 0, n - 1, 1), 0, n - 1, 0, 1) }
  sum(shift(a, 0, n - 1, 1), 0, n - 1, 0, 1)
    == sum(a, 1, n, 0, 1);

const x: [int]int;
const N: int;
axiom 2 < N;

lemma sum(shift(x[0 := x[1]][1 := x[0]], 0, N - 1, 1)[N - 1 := x[0 := x[1]][1 := x[0]][0]], 0, N, 0, 1)
        == sum(x, 0, N, 0, 1);
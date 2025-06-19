// from inclusive, to exclusive
function sum(a: [int]int, from: int, to: int, base: int, factor: int): int;

// normalize base and factor
free lemma forall a: [int]int, from: int, to: int, base: int, factor: int ::
    sum(a, from, to, base, factor) == sum(a, from, to, 0, 1) * factor + base;

// base case
free lemma forall a:[int]int ::
    sum(a, 0, 0, 0, 1) == 0;

// recursion
free lemma forall a: [int]int, to: int ::
    0 <= to ==> sum(a, 0, to+1, 0, 1) == sum(a, 0, to, 0, 1) + a[to];

free lemma forall a: [int]int, i: int, j: int, n: int, z: int ::
    0 <= i && i < n ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1) - a[i] + z;

free lemma forall a: [int]int, i: int, j: int, n: int, z: int ::
    i < 0 && 0 <= n ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1);
  
free lemma forall a: [int]int, i: int, j: int, n: int, z: int ::
    0 <= n && n <= i ==> sum(a[i:=z], 0, n, 0, 1) == sum(a, 0, n, 0, 1);

// from inclusive, to exclusive
function shift(a: [int]int, from: int, to: int, delta: int): [int]int;

free lemma forall a: [int]int, pos: int, delta: int ::
    shift(a, pos, pos, delta) == a;

free lemma forall a: [int]int, i: int, j: int, v: int ::
  !(1 <= j && j < i+1) && (0 <= j && j < i)
    ==> shift(a[j:=v], 0, i, 1) == shift(a, 0, i, 1);

free lemma forall a: [int]int, i: int, j: int, v: int ::
  !(1 <= j && j < i+1) && !(0 <= j && j < i)
    ==> shift(a[j:=v], 0, i, 1) == shift(a, 0, i, 1)[j:=v];

free lemma forall a: [int]int, i: int, j: int, v: int ::
  (1 <= j && j < i+1) && (0 <= j && j < i)
    ==> shift(a[j:=v], 0, i, 1) == shift(a, 0, i, 1)[j-1:=v];

free lemma forall a: [int]int, i: int, j: int, v: int ::
  (1 <= j && j < i+1) && !(0 <= j && j < i)
    ==> shift(a[j:=v], 0, i, 1) == shift(a, 0, i, 1)[j-1:=v][j:=v];


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

const N: int;
axiom 2 <= N;

procedure sum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant 0 <= i && i <= N;
    invariant ret == sum(x, 0, i, old(ret), 1);
  {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int := 0;

  while(i < N)
    decreases N - i;
    invariant 0 <= i && i <= N;
  {
    var nondet_int₂: int;
    x[i] := nondet_int₂;
    i := i + 1;
  }
  var sum₄: int;
  sum₄ := call sum(x);
  ret := sum₄;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var sum₅: int;
  sum₅ := call sum(x);
  ret2 := sum₅;
  temp := x[0];
  var i: int := 0;
  while(i < N - 1)
    decreases N - i;
    invariant 0 <= i && i <= N - 1;
    invariant x == shift(old(x), 0, i, 1);
  {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(N - 1)] := temp;
  var sum₇: int;
  sum₇ := call sum(x);
  ret5 := sum₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}


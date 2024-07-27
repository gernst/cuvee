data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var __VERIFIER_nondet_int₁₀₇₉: int;
  __VERIFIER_nondet_int₁₀₇₉ := call __VERIFIER_nondet_int();
  var j: int;
  j := __VERIFIER_nondet_int₁₀₇₉;
  assume j < 10000 && -10000 < j;
  var k: int;
  k := 0;
  var __VERIFIER_nondet_int₁₀₈₀: int;
  __VERIFIER_nondet_int₁₀₈₀ := call __VERIFIER_nondet_int();
  var N: int;
  N := __VERIFIER_nondet_int₁₀₈₀;
  assume N < 10000 && -10000 < N;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < N) {
    assume a[i] < 10000 && -10000 < a[i];
    if(a[i] < j) {
      j := a[i];
    }
    var x₁₀₈₁: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    b := b[i := a[i] - j];
    var x₁₀₈₂: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    k := k + b[i] + i;
    var x₁₀₈₃: int := i;
    i := i + 1;
  }
  assert 0 <= k;
  c#result := 0;
  return;
}


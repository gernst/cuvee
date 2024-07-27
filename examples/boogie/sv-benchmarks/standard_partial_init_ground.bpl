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
  var A: [int]int;
  var B: [int]int;
  var C: [int]int;
  var i: int;
  var j: int;
  j := 0;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₂₇₃: int;
    __VERIFIER_nondet_int₂₇₃ := call __VERIFIER_nondet_int();
    A := A[i := __VERIFIER_nondet_int₂₇₃];
    var __VERIFIER_nondet_int₂₇₄: int;
    __VERIFIER_nondet_int₂₇₄ := call __VERIFIER_nondet_int();
    B := B[i := __VERIFIER_nondet_int₂₇₄];
    var x₂₇₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    if(A[i] == B[i]) {
      C := C[j := i];
      j := j + 1;
    }
    var x₂₇₆: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < j) {
    assert C[x] <= x + i - j;
    var x₂₇₇: int := x;
    x := x + 1;
  }
  x := 0;
  while(x < j) {
    assert x <= C[x];
    var x₂₇₈: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


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
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₇₄: int;
    __VERIFIER_nondet_int₇₄ := call __VERIFIER_nondet_int();
    A := A[i := __VERIFIER_nondet_int₇₄];
    var x₇₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000 / 2) {
    A := A[i := A[100000 - i - 1]];
    var x₇₆: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000 / 2) {
    assert A[x] == A[100000 - x - 1];
    var x₇₇: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


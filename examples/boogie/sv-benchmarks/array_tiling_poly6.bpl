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
  var __VERIFIER_nondet_int₁₀₇₃: int;
  __VERIFIER_nondet_int₁₀₇₃ := call __VERIFIER_nondet_int();
  var S: int;
  S := __VERIFIER_nondet_int₁₀₇₃;
  assume 1 < S;
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < S) {
    a := a[i := (i - 1) * (i + 1)];
    var x₁₀₇₄: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < S) {
    a := a[i := a[i] - i * i];
    var x₁₀₇₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < S) {
    assert a[i] == -1;
    var x₁₀₇₆: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}


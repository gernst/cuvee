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
  var __VERIFIER_nondet_int₁₀₈₄: int;
  __VERIFIER_nondet_int₁₀₈₄ := call __VERIFIER_nondet_int();
  var j: int;
  j := __VERIFIER_nondet_int₁₀₈₄;
  var __VERIFIER_nondet_int₁₀₈₅: int;
  __VERIFIER_nondet_int₁₀₈₅ := call __VERIFIER_nondet_int();
  var n: int;
  n := __VERIFIER_nondet_int₁₀₈₅;
  assume n < 100000;
  var a: [int]int;
  assume 0 < j && j < 10000;
  i := 1;
  while(i < n) {
    var __VERIFIER_nondet_int₁₀₈₆: int;
    __VERIFIER_nondet_int₁₀₈₆ := call __VERIFIER_nondet_int();
    var k: int;
    k := __VERIFIER_nondet_int₁₀₈₆;
    assume 0 < k && k < 10000;
    a := a[i := i + j + k];
    var x₁₀₈₇: int := i;
    i := i + 1;
  }
  i := 1;
  while(i < n) {
    assert i + 2 <= a[i];
    var x₁₀₈₈: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}


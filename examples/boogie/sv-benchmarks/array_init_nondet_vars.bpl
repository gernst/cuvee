data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var __VERIFIER_nondet_int₁₀₈₄: int;
  var j: int;
  j := __VERIFIER_nondet_int₁₀₈₄;
  var __VERIFIER_nondet_int₁₀₈₅: int;
  var n: int;
  n := __VERIFIER_nondet_int₁₀₈₅;
  assume n < 100000;
  var a: [int]int;
  assume 0 < j && j < 10000;
  i := 1;
  while(i < n) {
    var __VERIFIER_nondet_int₁₀₈₆: int;
    var k: int;
    k := __VERIFIER_nondet_int₁₀₈₆;
    assume 0 < k && k < 10000;
    a := a[i := i + j + k];
    i := i + 1;
  }
  i := 1;
  while(i < n) {
    assert i + 2 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var __VERIFIER_nondet_int₃₂₁: int;
  var e: int;
  e := __VERIFIER_nondet_int₃₂₁;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₃₂₂: int;
    a := a[j := __VERIFIER_nondet_int₃₂₂];
    j := j + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000 && a[i] != e) {
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i) {
    assert a[x] != e;
    x := x + 1;
  }
  c#result := 0;
  return;
}


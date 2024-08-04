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
  var __VERIFIER_nondet_int₁: int;
  var marker: int;
  marker := __VERIFIER_nondet_int₁;
  var __VERIFIER_nondet_int₂: int;
  var pos: int;
  pos := __VERIFIER_nondet_int₂;
  var i: int := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₃: int;
    a := a[i := __VERIFIER_nondet_int₃];
    i := i + 1;
  }
  if(0 <= pos && pos < 100000) {
    a := a[pos := marker];
    var i: int := 0;
    while(a[i] != marker) {
      i := i + 1;
    }
    assert i <= pos;
  }
  c#result := 0;
  return;
}


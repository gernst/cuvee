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
  var array: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₂₃₄: int;
    __VERIFIER_nondet_int₂₃₄ := call __VERIFIER_nondet_int();
    array := array[i := __VERIFIER_nondet_int₂₃₄];
    var x₂₃₅: int := i;
    i := i + 1;
  }
  var largest: int;
  largest := array[0];
  i := 1;
  while(i < 100000) {
    if(largest < array[i]) {
      largest := array[i];
    }
    var x₂₃₆: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert array[x] <= largest;
    var x₂₃₇: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


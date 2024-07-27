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
  var a: [int]int;
  var min: int;
  min := 0;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₂₆₉: int;
    __VERIFIER_nondet_int₂₆₉ := call __VERIFIER_nondet_int();
    a := a[j := __VERIFIER_nondet_int₂₆₉];
    var x₂₇₀: int := j;
    j := j + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000) {
    if(a[i] < min) {
      min := a[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert min < a[x];
    var x₂₇₁: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


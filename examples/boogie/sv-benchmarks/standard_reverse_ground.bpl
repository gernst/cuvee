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
  var b: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₇₀: int;
    __VERIFIER_nondet_int₇₀ := call __VERIFIER_nondet_int();
    a := a[i := __VERIFIER_nondet_int₇₀];
    var x₇₁: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    b := b[i := a[100000 - i - 1]];
    var x₇₂: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a[x] == b[100000 - x - 1];
    var x₇₃: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


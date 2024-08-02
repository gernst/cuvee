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
  var b: [int]int;
  var __VERIFIER_nondet_int₁₀₁: int;
  var incr: int;
  incr := __VERIFIER_nondet_int₁₀₁;
  var i: int;
  i := 0;
  while(i < 100000) {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    b := b[i := b[i] + incr];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert b[x] == 42 + incr;
    x := x + 1;
  }
  c#result := 0;
  return;
}


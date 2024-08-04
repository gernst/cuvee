data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var aa: [int]int;
  var a: int := 0;
  var i: int := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  while(0 <= aa[a]) {
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < a) {
    assert 0 <= aa[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var src: [int]int;
  var dst: [int]int;
  var i: int;
  i := 0;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₂₄: int;
    src := src[j := __VERIFIER_nondet_int₂₄];
    j := j + 1;
  }
  while(i < 100000 && src[i] != 0) {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i) {
    assert dst[x] == src[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}


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
  var i: int := 0;
  var j: int := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₁: int;
    src := src[j := __VERIFIER_nondet_int₁];
    j := j + 1;
  }
  while(i < 100000 && src[i] != 0) {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000 && src[i] != 0) {
    assert dst[i] == src[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}


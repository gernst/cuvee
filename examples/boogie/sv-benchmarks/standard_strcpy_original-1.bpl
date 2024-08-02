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
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₃₅₇: int;
    src := src[i := __VERIFIER_nondet_int₃₅₇];
    i := i + 1;
  }
  i := 0;
  while(src[i] != 0) {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  i := 0;
  while(src[i] != 0) {
    assert dst[i] == src[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}


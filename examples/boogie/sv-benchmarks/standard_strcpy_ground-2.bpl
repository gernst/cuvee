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
  var src: [int]int;
  var dst: [int]int;
  var i: int;
  i := 0;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₃₀₉: int;
    __VERIFIER_nondet_int₃₀₉ := call __VERIFIER_nondet_int();
    src := src[i := __VERIFIER_nondet_int₃₀₉];
    var x₃₁₀: int := i;
    i := i + 1;
  }
  i := 0;
  while(src[i] != 0) {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i) {
    assert dst[x] == src[x];
    var x₃₁₁: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


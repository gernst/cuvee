data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure _strcmp(src: [int]int, dst: [int]int)
  returns (c#result: int)
{
  var i: int;
  i := 0;
  while(i < 100000) {
    if(dst[i] != src[i]) {
      c#result := 1;
      return;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₄₅: int;
    a := a[i := __VERIFIER_nondet_int₁₄₅];
    var __VERIFIER_nondet_int₁₄₆: int;
    b := b[i := __VERIFIER_nondet_int₁₄₆];
    i := i + 1;
  }
  var _strcmp₁₄₈: int;
  _strcmp₁₄₈ := call _strcmp(a, b);
  var c: int;
  c := _strcmp₁₄₈;
  if(c == 0) {
    var x: int;
    x := 0;
    while(x < 100000) {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure incrementArray(src: [int]int, dst: [int]int)
  returns (c#result: c#void)
{
  var i: int;
  i := 0;
  while(i < 100000) {
    dst := dst[i := src[i] + 1];
    i := i + 1;
  }
}

procedure main()
  returns (c#result: int)
{
  var src: [int]int;
  var dst: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₅₆: int;
    src := src[i := __VERIFIER_nondet_int₁₅₆];
    i := i + 1;
  }
  var incrementArray₁₅₈: c#void;
  incrementArray₁₅₈ := call incrementArray(src, dst);
  var x: int;
  x := 0;
  while(x < 100000) {
    src := src[x := dst[x] - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}


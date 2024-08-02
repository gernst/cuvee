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
  var c: [int]int;
  var i: int;
  i := 0;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₆₇: int;
    a := a[i := __VERIFIER_nondet_int₁₆₇];
    var __VERIFIER_nondet_int₁₆₈: int;
    b := b[i := __VERIFIER_nondet_int₁₆₈];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}


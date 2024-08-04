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
  var i: int := 0;
  var c: [int]int;
  var rv: int := 1;
  var j: int := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  while(i < 100000) {
    if(a[i] != b[i]) {
      rv := 0;
    }
    c := c[i := a[i]];
    i := i + 1;
  }
  var x: int;
  if(rv != 0) {
    x := 0;
    while(x < 100000) {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while(x < 100000) {
    assert a[x] == c[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}


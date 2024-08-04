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
  var j: int := 0;
  while(i < 10000) {
    var __VERIFIER_nondet_int₁: int;
    b := b[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 1;
  while(i < 10000) {
    a := a[j := b[i]];
    i := i + 3;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while(i < 10000) {
    assert a[j] == b[3 * j + 1];
    i := i + 3;
    j := j + 1;
  }
  c#result := 0;
  return;
}


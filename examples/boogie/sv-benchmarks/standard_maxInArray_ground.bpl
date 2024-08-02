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
  var max: int;
  max := 0;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₃₆₀: int;
    a := a[j := __VERIFIER_nondet_int₃₆₀];
    j := j + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000) {
    if(max < a[i]) {
      max := a[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a[x] <= max;
    x := x + 1;
  }
  c#result := 0;
  return;
}


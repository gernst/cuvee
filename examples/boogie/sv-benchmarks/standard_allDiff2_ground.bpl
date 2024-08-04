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
  var i: int;
  var r: int := 1;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 1;
  while(i < 100000 && r != 0) {
    var j: int;
    j := i - 1;
    while(0 <= j && r != 0) {
      if(a[i] == a[j]) {
        r := 1;
      }
      j := j - 1;
    }
    i := i + 1;
  }
  if(r != 0) {
    var x: int;
    var y: int;
    x := 0;
    while(x < 100000) {
      y := x + 1;
      while(y < 100000) {
        assert a[x] != a[y];
        y := y + 1;
      }
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}


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
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₃₆: int;
    a := a[j := __VERIFIER_nondet_int₃₆];
    j := j + 1;
  }
  var swapped: int;
  swapped := 1;
  while(swapped != 0) {
    swapped := 0;
    var i: int;
    i := 1;
    while(i < 100000) {
      if(a[i] < a[i - 1]) {
        var t: int;
        t := a[i];
        a := a[i := a[i - 1]];
        a := a[i - 1 := t];
        swapped := 1;
      }
      i := i + 1;
    }
  }
  var x: int;
  var y: int;
  x := 0;
  while(x < 100000) {
    y := x + 1;
    while(y < 100000) {
      assert a[x] <= a[y];
      y := y + 1;
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}


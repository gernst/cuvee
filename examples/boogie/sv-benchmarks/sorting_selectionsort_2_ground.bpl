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
  var i: int := 0;
  var x: int;
  var y: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    var k: int := i;
    var s: int := i + 1;
    while(k < 100000) {
      if(a[s] < a[k]) {
        s := k;
      }
      k := k + 1;
    }
    if(s != i) {
      var tmp: int := a[s];
      a := a[s := a[i]];
      a := a[i := tmp];
    }
    x := 0;
    while(x < i) {
      y := x + 1;
      while(y < i) {
        assert a[x] <= a[y];
        y := y + 1;
      }
      x := x + 1;
    }
    x := i + 1;
    while(x < 100000) {
      assert a[i] <= a[x];
      x := x + 1;
    }
    i := i + 1;
  }
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


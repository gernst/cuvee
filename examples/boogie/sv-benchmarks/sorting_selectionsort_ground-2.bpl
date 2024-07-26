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
  var a: [int]int;
  var i: int;
  i := 0;
  var x: int;
  var y: int;
  {
    var i: int;
    i := 0;
    while(i < 100000) {
      var __VERIFIER_nondet_int₁₂₇: int;
      __VERIFIER_nondet_int₁₂₇ := call __VERIFIER_nondet_int();
      a := a[i := __VERIFIER_nondet_int₁₂₇];
      var x₁₂₈: int := i;
      i := i + 1;
    }
  }
  i := 0;
  while(i < 100000) {
    var k: int;
    k := i + 1;
    var s: int;
    s := i;
    while(k < 100000) {
      if(a[k] < a[s]) {
        s := k;
      }
      k := k + 1;
    }
    if(s != i) {
      var tmp: int;
      tmp := a[s];
      a := a[s := a[i]];
      a := a[i := tmp];
    }
    x := 0;
    while(x < i) {
      y := x + 1;
      while(y < i) {
        assert a[x] <= a[y];
        var x₁₂₉: int := y;
        y := y + 1;
      }
      var x₁₃₀: int := x;
      x := x + 1;
    }
    x := i;
    while(x < 100000) {
      assert a[i] <= a[x];
      var x₁₃₁: int := x;
      x := x + 1;
    }
    i := i + 1;
  }
  x := 0;
  while(x < 100000) {
    y := x + 1;
    while(y < 100000) {
      assert a[x] <= a[y];
      var x₁₃₂: int := y;
      y := y + 1;
    }
    var x₁₃₃: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


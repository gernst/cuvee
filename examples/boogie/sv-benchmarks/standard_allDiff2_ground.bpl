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
  var r: int;
  r := 1;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₃₃₉: int;
    __VERIFIER_nondet_int₃₃₉ := call __VERIFIER_nondet_int();
    a := a[i := __VERIFIER_nondet_int₃₃₉];
    var x₃₄₀: int := i;
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
      var x₃₄₁: int := j;
      j := j - 1;
    }
    var x₃₄₂: int := i;
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
        var x₃₄₃: int := y;
        y := y + 1;
      }
      var x₃₄₄: int := x;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}


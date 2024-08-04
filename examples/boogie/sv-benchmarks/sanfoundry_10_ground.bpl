data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var n: int := 100000;
  var pos: int;
  var __VERIFIER_nondet_int₁: int;
  var element: int;
  element := __VERIFIER_nondet_int₁;
  var found: int := 0;
  var vectorx: [int]int;
  i := 0;
  while(i < n) {
    var __VERIFIER_nondet_int₂: int;
    vectorx := vectorx[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < n && !(found != 0)) {
    if(vectorx[i] == element) {
      found := 1;
      pos := i;
    }
    i := i + 1;
  }
  if(found != 0) {
    i := pos;
    while(i < n - 1) {
      vectorx := vectorx[i := vectorx[i + 1]];
      i := i + 1;
    }
  }
  if(found != 0) {
    var x: int;
    x := 0;
    while(x < pos) {
      assert vectorx[x] != element;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}


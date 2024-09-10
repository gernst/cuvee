data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  var i: int := 0;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    a[i] := nondet_int₁;
    var nondet_int₂: int;
    b[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    c[i] := a[i] - b[i];
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


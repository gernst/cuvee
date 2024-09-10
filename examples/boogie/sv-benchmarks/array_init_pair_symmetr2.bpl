data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 100000;
  var i: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < N) {
    var x: int;
    var y: int;
    assume y < 100000 && -100000 < y;
    assume x < 100000 && -100000 < x;
    assume y < x;
    a[i] := x;
    b[i] := y;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    c[i] := a[i] - b[i];
    i := i + 1;
  }
  i := 1;
  while(i < N) {
    assert 0 < c[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}


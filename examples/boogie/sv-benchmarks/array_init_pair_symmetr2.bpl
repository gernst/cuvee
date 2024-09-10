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
    assume -2147483648 <= x && x < 2147483648;
    var y: int;
    assume -2147483648 <= y && y < 2147483648;
    assume y < 100000 && -100000 < y;
    assume x < 100000 && -100000 < x;
    assume y < x;
    a := a[i := x];
    b := b[i := y];
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    c := c[i := a[i] - b[i]];
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


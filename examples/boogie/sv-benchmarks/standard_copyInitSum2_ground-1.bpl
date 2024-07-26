data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var a: [int]int;
  var b: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    b := b[i := a[i]];
    var x₁₃₇: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := b[i] + i];
    var x₁₃₈: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert b[x] == 42 + x;
    var x₁₃₉: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


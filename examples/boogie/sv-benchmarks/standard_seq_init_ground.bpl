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
  var i: int;
  i := 1;
  a := a[0 := 7];
  while(i < 100000) {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
  var x: int;
  x := 1;
  while(x < 100000) {
    assert a[x - 1] <= a[x];
    var x₂₂₁: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}


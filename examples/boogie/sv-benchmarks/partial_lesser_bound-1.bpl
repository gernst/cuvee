data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var a: [int]int;

var i: int;

procedure main()
  returns (c#result: int)
  modifies c#heap, a, i;
{
  i := 0;
  while(i < 10000000) {
    a := a[i := 0];
    var x₁₀₉₂: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2) {
    a := a[i := 10];
    var x₁₀₉₃: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2) {
    assert a[i] == 10;
    var x₁₀₉₄: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}


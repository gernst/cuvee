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
  var i: int;
  var N: int;
  N := 100000;
  var a: [int]int;
  i := 0;
  while(i <= N) {
    a := a[2 * i := 0];
    a := a[2 * i + 1 := 0];
    var x₁₀₇₇: int := i;
    i := i + 1;
  }
  i := 0;
  while(i <= 2 * N) {
    assert 0 <= a[i];
    var x₁₀₇₈: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}


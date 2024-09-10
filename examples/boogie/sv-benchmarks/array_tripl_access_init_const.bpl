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
  var i: int;
  var N: int := 100000;
  var a: [int]int;
  i := 0;
  while(i <= N) {
    a[(3 * i)] := 0;
    a[((3 * i) + 1)] := 0;
    a[((3 * i) + 2)] := 0;
    i := i + 1;
  }
  i := 0;
  while(i <= 3 * N) {
    assert 0 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}


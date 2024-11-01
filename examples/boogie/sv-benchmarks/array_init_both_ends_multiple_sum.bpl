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
  var a: [int]int;
  var b: [int]int;
  var i: int;
  var sum: int := 0;
  i := 0;
  while(i < N) {
    a[i] := i;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    b[((N - i) - 1)] := i;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    sum := sum + a[i] - b[N - i - 1];
    i := i + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(N <= 0) {
    c#result := 1;
    return;
  }
  assume N <= 2147483647 / 4;
  var i: int;
  var sum: [int]int;
  var a: [int]int;
  var b: [int]int;
  sum := sum[0 := 0];
  i := 0;
  while(i < N) {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    b := b[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    sum := sum[0 := sum[0] + b[i]];
    i := i + 1;
  }
  assert sum[0] <= 2 * N;
  c#result := 1;
  return;
}


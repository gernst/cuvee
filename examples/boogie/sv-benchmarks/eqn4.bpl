data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 0;
  havoc N;
  assume -2147483648 <= N && N < 2147483648;
  if(N <= 0) {
    c#result := 1;
    return;
  }
  assume N <= 2147483647 / 4;
  var i: int;
  var a: [int]int;
  var b: [int]int;
  a := a[0 := 8];
  b := b[0 := 1];
  i := 1;
  while(i < N) {
    a := a[i := a[i - 1] + 8];
    i := i + 1;
  }
  i := 1;
  while(i < N) {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    assert b[i] == 4 * i * i + 4 * i + 1;
    i := i + 1;
  }
  c#result := 1;
  return;
}


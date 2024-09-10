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
  var j: int;
  assume j < 10000 && -10000 < j;
  var k: int := 0;
  var N: int;
  assume N < 10000 && -10000 < N;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < N) {
    assume a[i] < 10000 && -10000 < a[i];
    if(a[i] < j) {
      j := a[i];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    b[i] := a[i] - j;
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    k := k + b[i] + i;
    i := i + 1;
  }
  assert 0 <= k;
  c#result := 0;
  return;
}


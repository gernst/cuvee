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
  var S: int;
  assume -2147483648 <= S && S < 2147483648;
  assume 1 < S;
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < S) {
    a := a[i := (i - 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < S) {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while(i < S) {
    assert a[i] == -1;
    i := i + 1;
  }
  c#result := 0;
  return;
}


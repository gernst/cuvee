data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var MAX: int;

var SIZE: int;

procedure main()
  returns (c#result: int)
  modifies MAX, SIZE;
{
  MAX := 100000;
  SIZE := 0;
  havoc SIZE;
  assume -2147483648 <= SIZE && SIZE < 2147483648;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var a: [int]int;
    var val2: int := 3;
    var val1: int := 7;
    var low: int := 2;
    i := SIZE - 2;
    while(-1 <= i) {
      if(0 <= i) {
        a[i] := val1;
      }
      a[(i + 1)] := val2;
      i := i - 1;
    }
    i := 0;
    while(i < SIZE) {
      assert low <= a[i];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}


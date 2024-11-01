data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var SIZE: int;

var MAX: int;

procedure main()
  returns (c#result: int)
  modifies SIZE, MAX;
{
  SIZE := 0;
  MAX := 100000;
  havoc SIZE;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var a: [int]int;
    var val2: int := 3;
    var val1: int := 0;
    var low: int := 2;
    i := 0;
    while(i < SIZE) {
      if(i + 1 < SIZE) {
        a[(i + 1)] := val1;
      }
      a[i] := val2;
      i := i + 1;
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


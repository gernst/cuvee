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
  var A: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    A[i] := nondet_int₁;
    i := i + 1;
  }
  i := 0;
  while(i < 100000 / 2) {
    A[i] := A[100000 - i - 1];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000 / 2) {
    assert A[x] == A[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}


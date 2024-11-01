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
  var B: [int]int;
  var C: [int]int;
  var i: int;
  var j: int := 0;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    A[i] := nondet_int₁;
    var nondet_int₂: int;
    B[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    if(A[i] == B[i]) {
      C[j] := i;
      j := j + 1;
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < j) {
    assert C[x] <= x + i - j;
    x := x + 1;
  }
  x := 0;
  while(x < j) {
    assert x <= C[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}


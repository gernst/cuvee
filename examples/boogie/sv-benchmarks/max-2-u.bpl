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
  var m: int := 1000;
  var n: int := 1500;
  var A: [int][int]int;
  var max: int;
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      A[i][j] := nondet_int₁;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  max := A[0][0];
  while(i < n) {
    j := 0;
    while(j < n) {
      if(max < A[i][j]) {
        max := A[i][j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < n) {
    j := 0;
    while(j < n) {
      assert A[i][j] <= max;
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

